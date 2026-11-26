/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.MSS
import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.RealStable
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bipartite Ramanujan graphs of every degree

Arbitrarily large `d`-regular bipartite Ramanujan graphs exist for every `d ≥ 3` (Marcus,
Spielman and Srivastava, *Interlacing families I: bipartite Ramanujan graphs of all degrees*,
Ann. of Math. 182 (2015), arXiv:1304.4132, Theorem 5.5). The proof takes repeated 2-lifts of the
complete bipartite graph `K_{d,d}`, choosing each signing through an interlacing family of
characteristic polynomials of signed adjacency matrices.

`exists_bipartite_ramanujan` implements this construction. To bound the signing, we evaluate the
mixed characteristic polynomial of the mean edge matrices by the matching polynomial recurrence.
Deleting a vertex bounds the ratio of the two evaluations above the Ramanujan threshold. The
characteristic polynomial of the lift then factors into the original and signed polynomials.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.RamanujanGraphsWanted

open scoped BigOperators ComplexOrder

-- A deleted neighbor leaves at most `d - 1` terms in the recurrence at a vertex.
private theorem pos_of_matchingRecurrence {V : Type*} [DecidableEq V]
    (adj : V → Finset V) (hsymm : ∀ ⦃v w⦄, w ∈ adj v → v ∈ adj w)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ v, (adj v).card ≤ d)
    (F : Finset V → ℝ) (x : ℝ) (hx : 2 * Real.sqrt ((d : ℝ) - 1) < x)
    (hempty : F ∅ = 1)
    (hrec : ∀ S v, v ∈ S →
      F S = x * F (S.erase v) - ∑ w ∈ (S.erase v) ∩ adj v, F ((S.erase v).erase w))
    (S : Finset V) : 0 < F S := by
  let c := Real.sqrt ((d : ℝ) - 1)
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 < c := Real.sqrt_pos_of_pos (by linarith)
  have hc₂ : c * c = (d : ℝ) - 1 := by
    rw [← pow_two, Real.sq_sqrt (by linarith)]
  have H (S : Finset V) :
      0 < F S ∧ ∀ v ∈ S, (∃ w ∈ adj v, w ∉ S) → c * F (S.erase v) ≤ F S := by
    refine Finset.strongInductionOn S ?_
    intro S ih
    have estimate (v : V) (hv : v ∈ S) :
        0 < F (S.erase v) ∧
          c * F S ≥ (c * x - (((S.erase v) ∩ adj v).card : ℝ)) * F (S.erase v) := by
      have hsub : S.erase v ⊂ S := Finset.erase_ssubset hv
      have hpos := (ih _ hsub).1
      refine ⟨hpos, ?_⟩
      rw [hrec S v hv, mul_sub, sub_mul, ← mul_assoc, Finset.mul_sum]
      apply sub_le_sub_left
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun w hw ↦ ?_
      obtain ⟨hwS, hwadj⟩ := Finset.mem_inter.mp hw
      exact (ih _ hsub).2 w hwS ⟨v, hsymm hwadj, Finset.notMem_erase v S⟩
    refine ⟨?_, ?_⟩
    · rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
      · simp [hempty]
      obtain ⟨hpos, hbound⟩ := estimate v hv
      have hcard : ((S.erase v ∩ adj v).card : ℝ) ≤ d := by
        exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans (hdeg v)
      have hcoef : 0 < c * x - ((S.erase v ∩ adj v).card : ℝ) := by
        have := mul_lt_mul_of_pos_left hx hc
        change c * (2 * c) < c * x at this
        nlinarith [hc₂]
      exact pos_of_mul_pos_right ((mul_pos hcoef hpos).trans_le hbound) hc.le
    · intro v hv hw
      obtain ⟨w, hwadj, hwS⟩ := hw
      obtain ⟨hpos, hbound⟩ := estimate v hv
      have hcard : ((S.erase v ∩ adj v).card : ℝ) + 1 ≤ d := by
        exact_mod_cast calc
          (S.erase v ∩ adj v).card + 1 = (insert w (S.erase v ∩ adj v)).card := by
            rw [Finset.card_insert_of_notMem (fun hw' ↦ hwS
              (Finset.mem_of_mem_erase (Finset.mem_inter.mp hw').1))]
          _ ≤ (adj v).card := Finset.card_le_card
            (Finset.insert_subset hwadj Finset.inter_subset_right)
          _ ≤ d := hdeg v
      have hcoef : c * c ≤ c * x - ((S.erase v ∩ adj v).card : ℝ) := by
        have := mul_lt_mul_of_pos_left hx hc
        change c * (2 * c) < c * x at this
        nlinarith [hc₂]
      exact le_of_mul_le_mul_left
        (by simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_right hcoef hpos.le).trans hbound) hc
  exact (H S).1

open Matrix

section Signing

open MvPolynomial
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger

private lemma mixed_mul_of_pderiv_eq_zero {σ : Type*} {p : MvPolynomial σ ℂ}
    (is : List σ) (hp : ∀ i ∈ is, pderiv i p = 0) (q : MvPolynomial σ ℂ) :
    mixedDifferential is (p * q) = p * mixedDifferential is q := by
  induction is generalizing q with
  | nil => rfl
  | cons i is ih =>
    rw [mixedDifferential_cons, pderiv_mul, hp i (by simp), zero_mul, zero_add,
      ← mul_sub, ih (fun j hj ↦ hp j (by simp [hj])), mixedDifferential_cons]

private noncomputable def mixedEval {σ : Type*} (is : List σ) (z : σ → ℂ) :
    MvPolynomial σ ℂ →+ ℂ where
  toFun p := MvPolynomial.eval z (mixedDifferential is p)
  map_zero' := by
    induction is with
    | nil => simp
    | cons i is ih => simpa [mixedDifferential_cons] using ih
  map_add' p q := by
    suffices ∀ p q : MvPolynomial σ ℂ,
      mixedDifferential is (p + q) = mixedDifferential is p + mixedDifferential is q by
      rw [this, map_add]
    clear p q
    induction is with
    | nil => simp
    | cons i is ih =>
      intro p q
      rw [mixedDifferential_cons, mixedDifferential_cons, mixedDifferential_cons, map_add,
        show p + q - (pderiv i p + pderiv i q) = p - pderiv i p + (q - pderiv i q) by abel,
        ih]

private lemma mixedEval_one {σ : Type*} (is : List σ) (z : σ → ℂ) : mixedEval is z 1 = 1 := by
  induction is with
  | nil => simp [mixedEval]
  | cons i is ih => simpa [mixedEval, mixedDifferential_cons] using ih

private lemma mixedEval_mul_of_pderiv_eq_zero {σ : Type*} {p : MvPolynomial σ ℂ}
    (is : List σ) (z : σ → ℂ) (hp : ∀ i ∈ is, pderiv i p = 0) (q : MvPolynomial σ ℂ) :
    mixedEval is z (p * q) = MvPolynomial.eval z p * mixedEval is z q := by
  simp only [mixedEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mixed_mul_of_pderiv_eq_zero is hp,
    map_mul]

-- At a zero edge variable, the factor `1 + X i` cancels the constant term of `1 - ∂ᵢ`.
private lemma mixedEval_one_add_X_mul {σ : Type*} [DecidableEq σ]
    (is : List σ) (hn : is.Nodup) (z : σ → ℂ) (i : σ) (hi : i ∈ is) (hz : z i = 0)
    (q : MvPolynomial σ ℂ) :
    mixedEval is z ((1 + X i) * q) = - mixedEval is z (pderiv i q)
      - mixedEval (is.erase i) z (pderiv i (pderiv i q)) := by
  have hperm : is.Perm (is.erase i ++ [i]) :=
    (List.perm_cons_erase hi).trans (List.perm_append_comm (l₁ := [i]) (l₂ := is.erase i))
  have h0 : ∀ j ∈ is.erase i, pderiv j (1 + X i : MvPolynomial σ ℂ) = 0 := by
    intro j hj
    have hji : i ≠ j := fun eq ↦ hn.not_mem_erase (eq ▸ hj)
    simp [pderiv_X_of_ne hji]
  simp only [mixedEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [mixedDifferential_eq_of_perm hperm ((1 + X i) * q),
    mixedDifferential_eq_of_perm hperm (pderiv i q)]
  simp only [mixedDifferential_append, mixedDifferential_cons, mixedDifferential_nil,
    mixed_mul_of_pderiv_eq_zero _ h0, pderiv_mul, map_add, pderiv_one, pderiv_X_self,
    zero_add, one_mul, map_sub, map_mul, MvPolynomial.eval_X, map_one, hz, add_zero]
  simp only [pderiv_mixedDifferential]
  ring

private lemma pderiv_prod_eq_zero {σ V : Type*} (i : σ) (f : V → MvPolynomial σ ℂ)
    (S : Finset V) (h : ∀ v ∈ S, pderiv i (f v) = 0) :
    pderiv i (∏ v ∈ S, f v) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert v S hv ih =>
    rw [Finset.prod_insert hv, pderiv_mul, h v (by simp),
      ih (fun w hw ↦ h w (by simp [hw]))]
    simp

section GraphPolynomial

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V}
variable {m : ℕ} (e : Fin m ≃ G.edgeSet)

private def edgeIndices (v : V) : Finset (Fin m) :=
  Finset.univ.filter (fun i ↦ v ∈ (e i).val)

private lemma mem_edgeIndices (v : V) (i : Fin m) : i ∈ edgeIndices e v ↔ v ∈ (e i).val := by
  simp [edgeIndices]

private def indexOfEdge {v w : V} (h : G.Adj v w) : Fin m :=
  e.symm ⟨s(v, w), h⟩

omit [DecidableEq V] in
private lemma indexOfEdge_spec {v w : V} (h : G.Adj v w) :
    (e (indexOfEdge e h)).val = s(v, w) := by simp [indexOfEdge]

private noncomputable def vertexFactor (d : ℕ) (v : V) : MvPolynomial (Unit ⊕ Fin m) ℂ :=
  (X (Sum.inl ()) - C (d : ℂ)) + ∑ i ∈ edgeIndices e v, (1 + X (Sum.inr i))

private lemma pderiv_vertexFactor (d : ℕ) (v : V) (i : Fin m) :
    pderiv (Sum.inr i) (vertexFactor e d v) = if v ∈ (e i).val then 1 else 0 := by
  classical
  simp only [vertexFactor, map_add, map_sub, pderiv_C, pderiv_X_of_ne Sum.inl_ne_inr,
    sub_zero, zero_add, map_sum, pderiv_one, pderiv_X, Pi.single_apply, Sum.inr.injEq]
  simp [mem_edgeIndices]

private lemma pderiv_vertexProduct (d : ℕ) {v w : V} (h : G.Adj v w)
    (S : Finset V) (hv : v ∉ S) :
    pderiv (Sum.inr (indexOfEdge e h)) (∏ u ∈ S, vertexFactor e d u) =
      if w ∈ S then ∏ u ∈ S.erase w, vertexFactor e d u else 0 := by
  classical
  have hzero (u : V) (hvu : u ≠ v) (hwu : u ≠ w) :
      pderiv (Sum.inr (indexOfEdge e h)) (vertexFactor e d u) = 0 := by
    simp [pderiv_vertexFactor, indexOfEdge_spec, Sym2.mem_iff, hvu, hwu]
  by_cases hw : w ∈ S
  · rw [ite_eq_left hw]
    conv_lhs => rw [← Finset.mul_prod_erase S (vertexFactor e d) hw]
    rw [pderiv_mul, pderiv_vertexFactor, indexOfEdge_spec, ite_eq_left (Sym2.mem_mk_right _ _),
      one_mul, pderiv_prod_eq_zero _ _ _ (fun u hu ↦
        hzero u (fun h ↦ hv (h ▸ Finset.mem_of_mem_erase hu)) (Finset.ne_of_mem_erase hu)),
      mul_zero, add_zero]
  · rw [ite_eq_right hw]
    exact pderiv_prod_eq_zero _ _ _ (fun u hu ↦ hzero u (fun h ↦ hv (h ▸ hu)) (fun h ↦ hw (h ▸ hu)))

private lemma pderiv_pderiv_vertexProduct (d : ℕ) {v w : V} (h : G.Adj v w)
    (S : Finset V) (hv : v ∉ S) :
    pderiv (Sum.inr (indexOfEdge e h))
      (pderiv (Sum.inr (indexOfEdge e h)) (∏ u ∈ S, vertexFactor e d u)) = 0 := by
  rw [pderiv_vertexProduct e d h S hv]
  split_ifs with hw
  · rw [pderiv_vertexProduct e d h (S.erase w) (fun hv' ↦ hv (Finset.mem_of_mem_erase hv')),
      ite_eq_right (Finset.notMem_erase w S)]
  · exact map_zero _

variable [Fintype V] [DecidableRel G.Adj]

private lemma sum_neighbors_edgeIndices {A : Type*} [AddCommMonoid A]
    (v : V) (f : V → A) (g : Fin m → A)
    (h : ∀ w (hw : G.Adj v w), f w = g (indexOfEdge e hw)) :
    ∑ w ∈ G.neighborFinset v, f w = ∑ i ∈ edgeIndices e v, g i := by
  apply Finset.sum_bij (fun w hw ↦ indexOfEdge e ((G.mem_neighborFinset v w).mp hw))
  · intro w hw
    rw [mem_edgeIndices, indexOfEdge_spec]
    exact Sym2.mem_mk_left _ _
  · intro w hw u hu eq
    have heq := congrArg (fun i ↦ (e i).val) eq
    rw [indexOfEdge_spec, indexOfEdge_spec] at heq
    exact Sym2.congr_right.mp heq
  · intro i hi
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp ((mem_edgeIndices e v i).mp hi)
    have hadj : G.Adj v w := by
      change s(v, w) ∈ G.edgeSet
      rw [← hw]
      exact (e i).prop
    refine ⟨w, (G.mem_neighborFinset v w).mpr hadj, e.injective ?_⟩
    apply Subtype.ext
    rw [indexOfEdge_spec, hw]
  · intro w hw
    exact h w ((G.mem_neighborFinset v w).mp hw)

private lemma card_edgeIndices (v : V) : (edgeIndices e v).card = G.degree v := by
  simpa using (sum_neighbors_edgeIndices e v (fun _ ↦ (1 : ℕ)) (fun _ ↦ 1)
    (fun _ _ ↦ rfl)).symm

private noncomputable def matchingValue (d : ℕ) (x : ℝ) (S : Finset V) : ℂ :=
  mixedEval ((List.finRange m).map Sum.inr) (Sum.elim (fun _ ↦ ((x : ℂ) + (d : ℂ))) (fun _ ↦ 0))
    (∏ u ∈ S, vertexFactor e d u)

omit [Fintype V] [DecidableRel G.Adj] in
private lemma matchingValue_empty (d : ℕ) (x : ℝ) : matchingValue e d x ∅ = 1 := by
  simp [matchingValue, mixedEval_one]

private lemma matchingValue_recurrence (d : ℕ) (x : ℝ) (S : Finset V) (v : V) (hv : v ∈ S) :
    matchingValue e d x S = (x : ℂ) * matchingValue e d x (S.erase v) -
      ∑ w ∈ S.erase v ∩ G.neighborFinset v, matchingValue e d x ((S.erase v).erase w) := by
  classical
  let is : List (Unit ⊕ Fin m) := (List.finRange m).map Sum.inr
  let z : Unit ⊕ Fin m → ℂ := Sum.elim (fun _ ↦ (x : ℂ) + (d : ℂ)) (fun _ ↦ 0)
  let T := S.erase v
  let q := ∏ u ∈ T, vertexFactor e d u
  unfold matchingValue
  rw [← Finset.mul_prod_erase S (vertexFactor e d) hv]
  change mixedEval is z (vertexFactor e d v * q) = _
  rw [vertexFactor, add_mul, Finset.sum_mul, map_add, map_sum]
  have hshift : ∀ i ∈ is,
      pderiv i (X (Sum.inl ()) - C (d : ℂ) : MvPolynomial (Unit ⊕ Fin m) ℂ) = 0 := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    simp
  rw [mixedEval_mul_of_pderiv_eq_zero is z hshift]
  simp only [map_sub, eval_X, eval_C, z, Sum.elim_inl, add_sub_cancel_right]
  rw [sub_eq_add_neg, add_right_inj, ← Finset.sum_neg_distrib]
  have hsum : (∑ w ∈ T ∩ G.neighborFinset v, -mixedEval is z
      (∏ u ∈ T.erase w, vertexFactor e d u)) =
      ∑ w ∈ G.neighborFinset v, -(if w ∈ T then mixedEval is z
        (∏ u ∈ T.erase w, vertexFactor e d u) else 0) := by
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w hw
    split_ifs <;> simp
  change _ = ∑ w ∈ T ∩ G.neighborFinset v, _
  rw [hsum]
  symm
  apply sum_neighbors_edgeIndices e
  intro w hw
  rw [mixedEval_one_add_X_mul is (List.nodup_finRange m |>.map Sum.inr_injective) z
    _ (by simp [is]) rfl,
    pderiv_pderiv_vertexProduct e d hw _ (Finset.notMem_erase v S), map_zero, sub_zero,
    pderiv_vertexProduct e d hw _ (Finset.notMem_erase v S)]
  split_ifs <;> simp [T]

private lemma matchingValue_re_pos {d : ℕ} (hd : 3 ≤ d) (hG : G.IsRegularOfDegree d)
    {x : ℝ} (hx : 2 * Real.sqrt ((d : ℝ) - 1) < x) (S : Finset V) :
    0 < (matchingValue e d x S).re := by
  refine pos_of_matchingRecurrence (fun v ↦ G.neighborFinset v) (fun {v w} hw ↦
    (G.mem_neighborFinset w v).mpr ((G.mem_neighborFinset v w).mp hw).symm) d hd
    (fun w ↦ by rw [SimpleGraph.card_neighborFinset_eq_degree, hG w])
    (fun T ↦ (matchingValue e d x T).re) x hx
    (by simp [matchingValue_empty]) ?_ S
  intro T w hw
  rw [matchingValue_recurrence e d x T w hw, Complex.sub_re, Complex.re_sum]
  simp [Complex.mul_re]

private noncomputable def signingValue (s : Fin 2) : ℝ := if s = 0 then 1 else -1

private lemma signingValue_zero : signingValue 0 = 1 := by simp [signingValue]
private lemma signingValue_one : signingValue 1 = -1 := by norm_num [signingValue]

private noncomputable def signedAdj (s : Fin m → Fin 2) : Matrix V V ℝ :=
  fun v w ↦ if h : G.Adj v w then signingValue (s (indexOfEdge e h)) else 0

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
private lemma indexOfEdge_symm {v w : V} (h : G.Adj v w) :
    indexOfEdge e h.symm = indexOfEdge e h := by
  unfold indexOfEdge
  congr 1
  exact Subtype.ext Sym2.eq_swap

private noncomputable def edgeVector (i : Fin m) (b : Fin 2) (v : V) : ℂ :=
  let endpoints := (e i).val.out
  if v = endpoints.1 then 1 else if v = endpoints.2 then (signingValue b : ℂ) else 0

private noncomputable def edgeOuter (i : Fin m) (b : Fin 2) : Matrix V V ℂ :=
  vecMulVec (edgeVector e i b) (star (edgeVector e i b))

omit [Fintype V] [DecidableRel G.Adj] in
private lemma edgeOuter_apply (i : Fin m) (b : Fin 2) (v w : V) :
    edgeOuter e i b v w = if v = w then (if v ∈ (e i).val then 1 else 0)
      else if v ∈ (e i).val ∧ w ∈ (e i).val then (signingValue b : ℂ) else 0 := by
  have hs := Sym2.mk_fst_out_snd_out (e i).val
  have hne : (e i).val.out.1 ≠ (e i).val.out.2 := by
    have ha := (e i).prop
    rw [← hs] at ha
    exact (show G.Adj (e i).val.out.1 (e i).val.out.2 from ha).ne
  have hh (u : V) : u ∈ (e i).val ↔ u = (e i).val.out.1 ∨ u = (e i).val.out.2 := by
    conv_lhs => rw [← hs]
    exact Sym2.mem_iff
  simp only [hh]
  fin_cases b <;>
    simp only [edgeOuter, edgeVector, Matrix.vecMulVec_apply, Pi.star_apply] <;>
    norm_num [signingValue] <;>
    split_ifs <;> simp_all [Ne.symm hne]

private lemma sum_edgeOuter (s : Fin m → Fin 2) {d : ℕ} (hG : G.IsRegularOfDegree d) :
    ∑ i, edgeOuter e i (s i) = (signedAdj e s).map Complex.ofReal + Matrix.scalar V (d : ℂ) := by
  classical
  ext v w
  simp only [Matrix.sum_apply, edgeOuter_apply, Matrix.add_apply, Matrix.map_apply]
  by_cases hvw : v = w
  · subst w
    simp only [ite_true, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    change ((edgeIndices e v).card : ℂ) = _
    rw [card_edgeIndices, hG v]
    simp [signedAdj, Matrix.natCast_apply]
  · simp only [hvw, ite_false, Matrix.scalar_apply, Matrix.diagonal_apply, add_zero]
    by_cases ha : G.Adj v w
    · rw [Finset.sum_eq_single (indexOfEdge e ha)]
      · simp [indexOfEdge_spec, signedAdj, ha]
      · intro i _ hi
        rw [ite_eq_right]
        rintro ⟨hv, hw⟩
        apply hi
        apply e.injective
        apply Subtype.ext
        rw [indexOfEdge_spec]
        exact (Sym2.mem_and_mem_iff hvw).mp ⟨hv, hw⟩
      · simp
    · have hi (i : Fin m) : ¬ (v ∈ (e i).val ∧ w ∈ (e i).val) := by
        intro hm
        have h := (Sym2.mem_and_mem_iff hvw).mp hm
        apply ha
        change s(v, w) ∈ G.edgeSet
        rw [← h]
        exact (e i).prop
      simp [hi, signedAdj, ha]

private noncomputable def meanOuter (i : Fin m) : Matrix V V ℂ :=
  ∑ b : Fin 2, (1 / 2 : ℝ) • edgeOuter e i b

omit [Fintype V] [DecidableRel G.Adj] in
private lemma meanOuter_eq_diagonal (i : Fin m) :
    meanOuter e i = Matrix.diagonal (fun v ↦ if v ∈ (e i).val then (1 : ℂ) else 0) := by
  ext v w
  simp only [meanOuter, Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_two, edgeOuter_apply,
    Matrix.diagonal_apply, signingValue_zero, signingValue_one, Complex.ofReal_one,
    Complex.ofReal_neg, Complex.real_smul]
  push_cast
  split_ifs <;> ring

omit [Fintype V] [DecidableRel G.Adj] in
private lemma meanOuter_posSemidef (i : Fin m) : (meanOuter e i).PosSemidef := by
  rw [meanOuter_eq_diagonal]
  rw [Matrix.posSemidef_diagonal_iff]
  intro v
  split_ifs <;> simp

private lemma mixedDet_meanOuter {d : ℕ} (hG : G.IsRegularOfDegree d) :
    mixedDetPolynomial (meanOuter e) = ∏ v, vertexFactor e d v := by
  classical
  unfold mixedDetPolynomial
  have hd : Matrix.scalar V (X (Sum.inl () : Unit ⊕ Fin m) : MvPolynomial (Unit ⊕ Fin m) ℂ) +
      (∑ i : Fin m, (X (Sum.inr i) : MvPolynomial (Unit ⊕ Fin m) ℂ) •
        (meanOuter e i).map (C : ℂ → MvPolynomial (Unit ⊕ Fin m) ℂ)) =
      Matrix.diagonal (vertexFactor e d) := by
    apply Matrix.ext
    intro v w
    simp only [Matrix.add_apply, Matrix.scalar_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.map_apply, meanOuter_eq_diagonal, Matrix.diagonal_apply]
    by_cases hvw : v = w
    · subst w
      simp only [ite_true, smul_eq_mul]
      simp_rw [apply_ite C, map_one, map_zero, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      change X (Sum.inl ()) + ∑ i ∈ edgeIndices e v, X (Sum.inr i) = vertexFactor e d v
      rw [vertexFactor, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        card_edgeIndices, hG v, map_natCast]
      ring
    · simp [hvw]
  rw [hd, Matrix.det_diagonal]

private lemma eval_mixedCharPoly_meanOuter {d : ℕ} (hG : G.IsRegularOfDegree d) (x : ℝ) :
    (mixedCharacteristicPolynomial (meanOuter e)).eval ((x : ℂ) + d) =
      matchingValue e d x Finset.univ := by
  unfold mixedCharacteristicPolynomial matchingValue
  rw [mixedDet_meanOuter e hG]
  let P := mixedDifferential (List.map Sum.inr (List.finRange m))
    (∏ u, vertexFactor e d u)
  change (((Polynomial.evalRingHom ((x : ℂ) + d)).comp
    (eval₂Hom Polynomial.C (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0)))) P) =
      MvPolynomial.eval (Sum.elim (fun _ ↦ (x : ℂ) + d) (fun _ ↦ 0)) P
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · rintro (_ | i) <;> simp

open Polynomial in
private lemma exists_signing_root_le [Nonempty V] {d : ℕ} (hd : 3 ≤ d)
    (hG : G.IsRegularOfDegree d) : ∃ s : Fin m → Fin 2, ∀ t : ℝ,
      (signedAdj e s).charpoly.IsRoot t → t ≤ 2 * Real.sqrt ((d : ℝ) - 1) := by
  classical
  let P := mixedCharacteristicPolynomial (meanOuter e)
  have hPmonic : P.Monic := mixedCharacteristicPolynomial_monic _
  have hProoted : P.IsRealRooted :=
    mixedCharacteristicPolynomial_isRealRooted_of_posSemidef _ (meanOuter_posSemidef e)
  have hPdeg : 0 < P.natDegree := by
    rw [show P.natDegree = Fintype.card V from mixedCharacteristicPolynomial_natDegree _]
    exact Fintype.card_pos
  have hmax : P.maxRealRoot ≤ 2 * Real.sqrt ((d : ℝ) - 1) + d := by
    by_contra! h
    let x : ℝ := P.maxRealRoot - d
    have hx : 2 * Real.sqrt ((d : ℝ) - 1) < x := by dsimp [x]; linarith
    have heval := eval_mixedCharPoly_meanOuter e hG x
    change P.eval ((x : ℂ) + d) = _ at heval
    have hshift : (x : ℂ) + d = (P.maxRealRoot : ℂ) := by simp [x]
    have hroot := (mem_roots hPmonic.ne_zero).mp (coe_maxRealRoot_mem_roots hProoted hPdeg)
    have hvalue : P.eval ((x : ℂ) + d) = 0 := by rwa [hshift]
    rw [hvalue] at heval
    have hpos := matchingValue_re_pos e hd hG hx Finset.univ
    rw [← heval] at hpos
    simp at hpos
  obtain ⟨s, hs⟩ := exists_outcome_maxRealRoot_le_mixedCharacteristicPolynomial
    (s := fun _ : Fin m ↦ 2) (by simp) (fun _ _ ↦ 1 / 2) (edgeVector e)
    (by intro i b; positivity) (by simp)
  change (∑ i, edgeOuter e i (s i)).charpoly.maxRealRoot ≤ P.maxRealRoot at hs
  refine ⟨s, fun t ht ↦ ?_⟩
  rw [sum_edgeOuter e s hG] at hs
  let A := (signedAdj e s).map Complex.ofReal + Matrix.scalar V (d : ℂ)
  change A.charpoly.maxRealRoot ≤ P.maxRealRoot at hs
  have hchar : (A - Matrix.scalar V (d : ℂ)).charpoly =
      (signedAdj e s).charpoly.map Complex.ofRealHom := by
    rw [show A - Matrix.scalar V (d : ℂ) = (signedAdj e s).map Complex.ofRealHom by
      simp [A]; rfl, Matrix.charpoly_map]
  have hroot : A.charpoly.IsRoot ((t : ℂ) + d) := by
    rw [Matrix.charpoly_sub_scalar] at hchar
    have h := congrArg (fun p : Polynomial ℂ ↦ p.eval (t : ℂ)) hchar
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C] at h
    rw [show (t : ℂ) = Complex.ofRealHom t from rfl, Polynomial.eval_map_apply, ht, map_zero] at h
    exact h
  have hle := (root_re_le_maxRealRoot ((mem_roots A.charpoly_monic.ne_zero).mpr hroot)).trans
    (hs.trans hmax)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re] at hle
  linarith

omit [DecidableRel G.Adj] in
open Polynomial in
private lemma isRoot_neg_of_supported {A : Matrix V V ℝ} (c : G.Coloring (Fin 2))
    (hA : ∀ v w, ¬ G.Adj v w → A v w = 0) {t : ℝ} (ht : A.charpoly.IsRoot t) :
    A.charpoly.IsRoot (-t) := by
  classical
  let D : Matrix V V ℝ := diagonal (signingValue ∘ c)
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun v _ ↦ by by_cases hv : c v = 0 <;>
      simp [signingValue, hv])
  have hcomm : A * D = D * (-A) := by
    ext v w
    simp only [D, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, Function.comp_apply]
    by_cases ha : G.Adj v w
    · have hneq := c.valid ha
      by_cases hv : c v = 0
      · have hw : c w ≠ 0 := fun hw ↦ hneq (hv.trans hw.symm)
        simp [signingValue, hv, hw]
      · have hw : c w = 0 := by
          have h1 : c v = 1 := by omega
          omega
        simp [signingValue, hv, hw]
    · rw [hA v w ha]
      simp
  have hchar := Matrix.charpoly_eq_of_mul_eq_mul hD hcomm
  change A.charpoly.eval t = 0 at ht
  rw [hchar, Matrix.eval_charpoly] at ht
  change A.charpoly.eval (-t) = 0
  rw [Matrix.eval_charpoly, show Matrix.scalar V (-t) - A =
    -(Matrix.scalar V t - (-A)) by
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
      ring]
  rw [Matrix.det_neg, ht, mul_zero]

private def signSubgraph (s : Fin m → Fin 2) (positive : Prop) [Decidable positive] :
    SimpleGraph V where
  Adj v w := ∃ h : G.Adj v w, (s (indexOfEdge e h) = 0 ↔ positive)
  symm.symm v w := by
    rintro ⟨h, hsign⟩
    exact ⟨h.symm, by rwa [indexOfEdge_symm]⟩
  loopless.irrefl v := fun ⟨h, _⟩ ↦ G.loopless.irrefl v h

private instance signSubgraphDecidableAdj (s : Fin m → Fin 2) (positive : Prop)
    [Decidable positive] : DecidableRel (signSubgraph e s positive).Adj :=
  fun v w ↦ inferInstanceAs (Decidable (∃ h : G.Adj v w,
    (s (indexOfEdge e h) = 0 ↔ positive)))

omit [DecidableEq V] [Fintype V] in
private lemma adjMatrix_signSubgraph_add (s : Fin m → Fin 2) :
    (signSubgraph e s True).adjMatrix ℝ + (signSubgraph e s False).adjMatrix ℝ =
      G.adjMatrix ℝ := by
  ext v w
  by_cases ha : G.Adj v w
  · by_cases hb : s (indexOfEdge e ha) = 0 <;>
      simp [signSubgraph, SimpleGraph.adjMatrix_apply, ha, hb]
  · simp [signSubgraph, SimpleGraph.adjMatrix_apply, ha]

omit [DecidableEq V] [Fintype V] in
private lemma adjMatrix_signSubgraph_sub (s : Fin m → Fin 2) :
    (signSubgraph e s True).adjMatrix ℝ - (signSubgraph e s False).adjMatrix ℝ =
      signedAdj e s := by
  ext v w
  by_cases ha : G.Adj v w
  · by_cases hb : s (indexOfEdge e ha) = 0 <;>
      simp [signSubgraph, SimpleGraph.adjMatrix_apply, ha, hb, signedAdj, signingValue]
  · simp [signSubgraph, SimpleGraph.adjMatrix_apply, ha, signedAdj]

private def twoLift (s : Fin m → Fin 2) : SimpleGraph (V ⊕ V) :=
  (signSubgraph e s True).sum (signSubgraph e s True) ⊔
    (signSubgraph e s False).bipartiteDoubleCover

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
private lemma twoLift_adj_iff (s : Fin m → Fin 2) (a b : V ⊕ V) :
    (twoLift e s).Adj a b ↔
      (signSubgraph e s (a.isLeft = b.isLeft)).Adj (Sum.elim id id a) (Sum.elim id id b) := by
  cases a <;> cases b <;> simp [twoLift, signSubgraph]

private instance twoLiftDecidableAdj (s : Fin m → Fin 2) : DecidableRel (twoLift e s).Adj :=
  fun a b ↦ decidable_of_iff _ (twoLift_adj_iff e s a b).symm

omit [DecidableEq V] [Fintype V] in
private lemma adjMatrix_twoLift (s : Fin m → Fin 2) :
    (twoLift e s).adjMatrix ℝ = fromBlocks
      ((signSubgraph e s True).adjMatrix ℝ) ((signSubgraph e s False).adjMatrix ℝ)
      ((signSubgraph e s False).adjMatrix ℝ) ((signSubgraph e s True).adjMatrix ℝ) := by
  ext (v | v) (w | w) <;> simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, SimpleGraph.adjMatrix_apply] <;>
    simp [twoLift]

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
private lemma colorable_twoLift (s : Fin m → Fin 2) (c : G.Colorable 2) :
    (twoLift e s).Colorable 2 := by
  obtain ⟨c⟩ := c
  refine ⟨SimpleGraph.Coloring.mk (Sum.elim c c) ?_⟩
  intro a b h
  have hbase := ((twoLift_adj_iff e s a b).mp h).1
  cases a <;> cases b <;> exact c.valid hbase

omit [DecidableEq V] in
private lemma regular_twoLift (s : Fin m → Fin 2) {d : ℕ} (hG : G.IsRegularOfDegree d) :
    (twoLift e s).IsRegularOfDegree d := by
  intro a
  have h := (twoLift e s).adjMatrix_mulVec_const_apply (α := ℝ) (a := 1) (v := a)
  rw [adjMatrix_twoLift e s, fromBlocks_mulVec] at h
  have h' (v : V) := congrFun (congrArg (fun A : Matrix V V ℝ ↦
    A *ᵥ Function.const V 1) (adjMatrix_signSubgraph_add e s)) v
  simp only [Matrix.add_mulVec, Pi.add_apply,
    SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hG, mul_one] at h'
  simp only [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one] at h'
  have hx : (((twoLift e s).degree a : ℕ) : ℝ) = (d : ℝ) := by
    cases a with
    | inl v => simpa [h' v] using h.symm
    | inr v =>
      have hv := h' v
      rw [add_comm] at hv
      simpa [hv] using h.symm
  exact_mod_cast hx

end GraphPolynomial

end Signing

private lemma charpoly_fromBlocks_symm {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Matrix V V ℝ) : (fromBlocks P Q Q P).charpoly =
      (P + Q).charpoly * (P - Q).charpoly := by
  let T : Matrix (V ⊕ V) (V ⊕ V) ℝ := fromBlocks 1 1 1 (-1)
  have hT : T.det ≠ 0 := by
    have hSq : T * T = (2 : ℝ) • (1 : Matrix (V ⊕ V) (V ⊕ V) ℝ) := by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
      simp [T, Matrix.fromBlocks_multiply, two_smul]
    intro hz
    have h := congrArg det hSq
    rw [Matrix.det_mul, hz, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h
    exact (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) h.symm
  rw [← Matrix.charpoly_fromBlocks_zero₁₂ (M₂₁ := (0 : Matrix V V ℝ))]
  apply Matrix.charpoly_eq_of_mul_eq_mul hT
  simp [T, Matrix.fromBlocks_multiply, add_comm, sub_eq_add_neg]

private lemma charpoly_twoLift {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {m : ℕ} (e : Fin m ≃ G.edgeSet) (s : Fin m → Fin 2) :
    ((twoLift e s).adjMatrix ℝ).charpoly = (G.adjMatrix ℝ).charpoly * (signedAdj e s).charpoly := by
  rw [adjMatrix_twoLift e s, charpoly_fromBlocks_symm, adjMatrix_signSubgraph_add e s,
    adjMatrix_signSubgraph_sub e s]

-- This factorization records the multiplicities of the exceptional eigenvalues.
open Polynomial in
private def RamanujanCharpoly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∃ p : Polynomial ℝ, (G.adjMatrix ℝ).charpoly = (X - C (d : ℝ)) * (X + C (d : ℝ)) * p ∧
    ∀ t ∈ p.roots, |t| ≤ 2 * Real.sqrt ((d : ℝ) - 1)

open Classical in
private lemma base_regular (d : ℕ) :
    (completeBipartiteGraph (Fin d) (Fin d)).IsRegularOfDegree d := by
  classical
  let G := completeBipartiteGraph (Fin d) (Fin d)
  intro v
  have he := G.adjMatrix_mulVec_const_apply (α := ℝ) (a := 1) (v := v)
  have hsum : (G.adjMatrix ℝ *ᵥ Function.const _ 1) v = (d : ℝ) := by
    simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one, Fintype.sum_sum_type]
    cases v <;> simp [G, SimpleGraph.adjMatrix_apply]
  rw [hsum, mul_one] at he
  exact_mod_cast he.symm

private lemma base_colorable (d : ℕ) :
    (completeBipartiteGraph (Fin d) (Fin d)).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)) ?_⟩
  rintro (a | a) (b | b) h <;> simp_all

open Polynomial Classical in
private lemma base_charpoly (d : ℕ) (hd : 3 ≤ d) :
    RamanujanCharpoly (completeBipartiteGraph (Fin d) (Fin d)) d := by
  classical
  let G := completeBipartiteGraph (Fin d) (Fin d)
  let U : Matrix (Fin d ⊕ Fin d) (Fin 2) ℝ := Matrix.of fun
    | .inl _, i => if i = 0 then 1 else 0
    | .inr _, i => if i = 0 then 0 else 1
  let W : Matrix (Fin 2) (Fin d ⊕ Fin d) ℝ := Matrix.of fun
    | i, .inl _ => if i = 0 then 0 else 1
    | i, .inr _ => if i = 0 then 1 else 0
  have hA : G.adjMatrix ℝ = U * W := by
    ext (v | v) (w | w) <;>
      simp [G, U, W, SimpleGraph.adjMatrix_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have hB : W * U = !![(0 : ℝ), d; d, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [U, W, Matrix.mul_apply, Fintype.sum_sum_type]
  have hchar : (W * U).charpoly = (X - C (d : ℝ)) * (X + C (d : ℝ)) := by
    rw [hB, Matrix.charpoly, Matrix.det_fin_two, Matrix.charmatrix_apply_eq,
      Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne _ _ _ (by decide),
      Matrix.charmatrix_apply_ne _ _ _ (by decide)]
    simp
    ring
  refine ⟨X ^ (Fintype.card (Fin d ⊕ Fin d) - 2), ?_, ?_⟩
  · change (G.adjMatrix ℝ).charpoly = _
    rw [hA, Matrix.charpoly_mul_comm_of_le U W (by simp; omega), hchar, mul_comm,
      Fintype.card_fin]
  · intro t ht
    have hroot := (Polynomial.mem_roots (pow_ne_zero _ Polynomial.X_ne_zero)).mp ht
    rw [Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_X] at hroot
    rw [eq_zero_of_pow_eq_zero hroot, abs_zero]
    positivity

private lemma overFin_data {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d n : ℕ} (hn : Fintype.card V = n) (hG : G.IsRegularOfDegree d)
    (hc : G.Colorable 2) (hchar : RamanujanCharpoly G d) :
    open Classical in
    (G.overFin hn).IsRegularOfDegree d ∧ (G.overFin hn).Colorable 2 ∧
      RamanujanCharpoly (G.overFin hn) d := by
  classical
  let f := G.overFinIso hn
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have h := Fintype.card_congr (f.symm.mapNeighborSet v)
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree, hG] at h
    exact h
  · obtain ⟨c⟩ := hc
    exact ⟨c.comp f.symm.toRelEmbedding.toRelHom⟩
  · rcases hchar with ⟨p, hp, hb⟩
    refine ⟨p, ?_, hb⟩
    rw [← f.reindex_adjMatrix ℝ, Matrix.charpoly_reindex, hp]

open Polynomial in
private lemma ramanujanCharpoly_twoLift {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {m : ℕ} (e : Fin m ≃ G.edgeSet) {d : ℕ} (s : Fin m → Fin 2)
    (hG : RamanujanCharpoly G d) (c : G.Coloring (Fin 2))
    (hs : ∀ t : ℝ, (signedAdj e s).charpoly.IsRoot t → t ≤ 2 * Real.sqrt ((d : ℝ) - 1)) :
    RamanujanCharpoly (twoLift e s) d := by
  obtain ⟨p, hp, hb⟩ := hG
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hp
    exact (G.adjMatrix ℝ).charpoly_monic.ne_zero hp
  refine ⟨p * (signedAdj e s).charpoly, ?_, ?_⟩
  · rw [charpoly_twoLift, hp, mul_assoc]
  · rw [roots_mul (mul_ne_zero hp0 (signedAdj e s).charpoly_monic.ne_zero)]
    intro t ht
    rcases Multiset.mem_add.mp ht with ht | ht
    · exact hb t ht
    · have hroot := (mem_roots (signedAdj e s).charpoly_monic.ne_zero).mp ht
      rw [abs_le]
      refine ⟨?_, hs t hroot⟩
      have hneg := hs (-t) (isRoot_neg_of_supported c (fun v w hw ↦ by simp [signedAdj, hw]) hroot)
      linarith

open Classical in
private lemma exists_large_ramanujanCharpoly (d : ℕ) (hd : 3 ≤ d) (N : ℕ) :
    ∃ n ≥ N, 0 < n ∧ ∃ G : SimpleGraph (Fin n),
      G.IsRegularOfDegree d ∧ G.Colorable 2 ∧ RamanujanCharpoly G d := by
  classical
  induction N with
  | zero =>
    let G := completeBipartiteGraph (Fin d) (Fin d)
    let n := Fintype.card (Fin d ⊕ Fin d)
    have hn : 0 < n := by simp [n]; omega
    obtain ⟨h₁, h₂, h₃⟩ := overFin_data G (n := n) rfl
      (base_regular d) (base_colorable d) (base_charpoly d hd)
    exact ⟨n, Nat.zero_le _, hn, G.overFin rfl, h₁, h₂, h₃⟩
  | succ N ih =>
    obtain ⟨n, hn, hnpos, G, hG, ⟨c⟩, hp⟩ := ih
    let _ : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    let e := (Fintype.equivFin G.edgeSet).symm
    obtain ⟨s, hs⟩ := exists_signing_root_le e hd hG
    have hcard : Fintype.card (Fin n ⊕ Fin n) = n + n := by simp
    obtain ⟨h₁, h₂, h₃⟩ := overFin_data (twoLift e s) hcard
      (regular_twoLift e s hG) (colorable_twoLift e s ⟨c⟩) (ramanujanCharpoly_twoLift e s hp c hs)
    exact ⟨n + n, by omega, by omega, (twoLift e s).overFin hcard, h₁, h₂, h₃⟩

private lemma ramanujan_bound_lt {d : ℕ} (hd : 3 ≤ d) :
    2 * Real.sqrt ((d : ℝ) - 1) < (d : ℝ) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : (2 * Real.sqrt ((d : ℝ) - 1)) ^ 2 = 4 * ((d : ℝ) - 1) := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    ring
  by_contra! h
  have hle := mul_self_le_mul_self (by positivity : 0 ≤ (d : ℝ)) h
  nlinarith [sq_nonneg ((d : ℝ) - 3)]

open Polynomial in
private lemma eigenvalues₀_bound_of_ramanujanCharpoly {n d : ℕ} (hd : 3 ≤ d)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RamanujanCharpoly G d)
    (i : Fin (Fintype.card (Fin n))) (hi₀ : (i : ℕ) ≠ 0) (hin : (i : ℕ) + 1 ≠ n) :
    |(G.isHermitian_adjMatrix (R := ℝ)).eigenvalues₀ i| ≤ 2 * Real.sqrt ((d : ℝ) - 1) := by
  classical
  let ev := (G.isHermitian_adjMatrix (R := ℝ)).eigenvalues₀
  let B := 2 * Real.sqrt ((d : ℝ) - 1)
  have hB := ramanujan_bound_lt hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨p, hp, hpbound⟩ := hG
  have hpn : (X - C (d : ℝ)) * (X + C (d : ℝ)) * p ≠ 0 :=
    hp ▸ (G.adjMatrix ℝ).charpoly_monic.ne_zero
  have hroots : (G.adjMatrix ℝ).charpoly.roots = {((d : ℕ) : ℝ)} + {-((d : ℕ) : ℝ)} + p.roots := by
    rw [hp, roots_mul hpn, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_add_C_ne_zero _)),
      roots_X_sub_C, roots_X_add_C]
  have heq : (G.adjMatrix ℝ).charpoly.roots = Finset.univ.val.map ev := by
    simpa [ev] using (G.isHermitian_adjMatrix (R := ℝ)).roots_charpoly_eq_eigenvalues₀
  have hcases (j : Fin (Fintype.card (Fin n))) :
      ev j = (d : ℝ) ∨ ev j = -(d : ℝ) ∨ |ev j| ≤ B := by
    have hj : ev j ∈ (G.adjMatrix ℝ).charpoly.roots := by
      rw [heq]
      exact Multiset.mem_map.mpr ⟨j, by simp, rfl⟩
    rw [hroots] at hj
    rcases Multiset.mem_add.mp hj with hj | hj
    · simpa [Multiset.mem_add, or_assoc] using (Or.inl hj :
        ev j ∈ ({(d : ℝ)} + {-(d : ℝ)} : Multiset ℝ) ∨ |ev j| ≤ B)
    · exact Or.inr (Or.inr (hpbound _ hj))
  have hcount (t : ℝ) (ht : |t| > B) (h : t = d ∨ t = -(d : ℝ)) :
      (Finset.univ.filter (fun j ↦ ev j = t)).card = 1 := by
    have hout : t ∉ p.roots := fun hm ↦ (not_le_of_gt ht) (hpbound _ hm)
    have he := congrArg (Multiset.count t) (heq.symm.trans hroots)
    rw [Multiset.count_map, Multiset.count_add, Multiset.count_add,
      Multiset.count_eq_zero_of_notMem hout, add_zero] at he
    simp only [eq_comm (a := t), ← Finset.filter_val] at he
    have hne : (d : ℝ) ≠ -(d : ℝ) := by linarith
    rcases h with rfl | rfl <;>
      simpa only [Multiset.count_singleton, ite_eq_left rfl, ite_eq_right hne,
        ite_eq_right hne.symm, ite_true, Finset.card, zero_add, add_zero] using he
  have hunique {t : ℝ} (ht : |t| > B) (htd : t = d ∨ t = -(d : ℝ))
      {j k : Fin (Fintype.card (Fin n))} (hj : ev j = t) (hk : ev k = t) : j = k := by
    by_contra! h
    have htwo : 1 < (Finset.univ.filter (fun a ↦ ev a = t)).card :=
      Finset.one_lt_card.mpr ⟨j, by simp [hj], k, by simp [hk], h⟩
    rw [hcount t ht htd] at htwo
    omega
  have hm : Antitone ev := (G.isHermitian_adjMatrix (R := ℝ)).eigenvalues₀_antitone
  change |ev i| ≤ B
  rcases hcases i with hi | hi | hi
  · let j : Fin (Fintype.card (Fin n)) := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
    have hle := hm (show j ≤ i by exact Nat.zero_le _)
    have hj : ev j = (d : ℝ) := by
      rw [hi] at hle
      rcases hcases j with h | h | h
      · exact h
      · linarith
      · have hb := (abs_le.mp h).2
        change B < (d : ℝ) at hB
        linarith
    have he := hunique (t := (d : ℝ)) (by rw [abs_of_pos hdpos]; exact hB) (Or.inl rfl) hi hj
    exact (hi₀ (congrArg Fin.val he)).elim
  · let j : Fin (Fintype.card (Fin n)) := ⟨Fintype.card (Fin n) - 1, by have := i.isLt; omega⟩
    have hle := hm (show i ≤ j by change (i : ℕ) ≤ Fintype.card (Fin n) - 1; omega)
    have hj : ev j = -(d : ℝ) := by
      rw [hi] at hle
      rcases hcases j with h | h | h
      · linarith
      · exact h
      · have hb := (abs_le.mp h).1
        change B < (d : ℝ) at hB
        linarith
    have he := hunique (t := -(d : ℝ)) (by rw [abs_neg, abs_of_pos hdpos]; exact hB)
      (Or.inr rfl) hi hj
    have hv := congrArg Fin.val he
    change (i : ℕ) = Fintype.card (Fin n) - 1 at hv
    simp only [Fintype.card_fin] at hv
    exact (hin (by have := i.isLt; simp only [Fintype.card_fin] at this; omega)).elim
  · exact hi

open Classical in
/-- **Bipartite Ramanujan graphs of every degree.** For every `d ≥ 3` there are arbitrarily large
`d`-regular bipartite Ramanujan graphs: `d`-regular bipartite graphs whose adjacency eigenvalues,
other than the largest (`d`) and the smallest (`-d`), all lie in `[-2√(d - 1), 2√(d - 1)]`
(Marcus, Spielman and Srivastava, *Interlacing families I: bipartite Ramanujan graphs of all
degrees*, arXiv:1304.4132, Theorem 5.5, with the definition of Section 2.1). -/
theorem exists_bipartite_ramanujan (d : ℕ) (hd : 3 ≤ d) (N : ℕ) :
    ∃ n ≥ N, ∃ G : SimpleGraph (Fin n), G.IsRegularOfDegree d ∧ G.Colorable 2 ∧
      ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) ≠ 0 → (i : ℕ) + 1 ≠ n →
        |(G.isHermitian_adjMatrix (R := ℝ)).eigenvalues₀ i| ≤ 2 * Real.sqrt ((d : ℝ) - 1) := by
  obtain ⟨n, hn, _, G, hG, hc, hp⟩ := exists_large_ramanujanCharpoly d hd N
  exact ⟨n, hn, G, hG, hc, eigenvalues₀_bound_of_ramanujanCharpoly hd G hp⟩

end MathlibExt.GraphTheory.RamanujanGraphsWanted
