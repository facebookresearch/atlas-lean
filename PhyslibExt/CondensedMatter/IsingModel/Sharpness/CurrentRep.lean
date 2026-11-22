/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.GKS
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.RandomCurrent

/-!
# The random-current representation

Correlations of the finite Ising model with couplings `J` are ratios of current sums: `⟨σ_A⟩_{β,J} =
Z(∂ = A)/Z(∂ = ∅)`.

## i. Overview

Expanding each factor `exp(βJ_e σ_xσ_y) = ∑_k (βJ_e)^k (σ_xσ_y)^k / k!` and exchanging the finite
product with the series (`prod_tsum_fubini`) writes the Boltzmann weight as a sum over currents.
Summing `σ_A ∏_e (σ_e)^{n_e}` over configurations gives `2^{|V|}` if `∂n = A` and `0` otherwise.
Hence `∑_σ σ_A e^{-βH(σ)} = 2^{|V|} Z(∂ = A)`, and dividing by the partition function gives the
representation.

## ii. Key results

- `prod_tsum_fubini` : products of series as series over functions
- `spinSum_monomial_eq` : spin sums of monomials select the source set
- `currentSum` : the current sum `Z(∂ = A)`
- `expectationJ` : correlations with couplings `J`
- `current_representation` : the random-current representation
- `isingExpectation_eq_currentSum_ratio` : the representation at uniform coupling and zero field

## iii. Table of contents

- A. Products of series
- B. Spin sums of monomials
- C. Current sums
- D. The representation

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48
- H. Duminil-Copin, "Random currents expansion of the Ising model", lecture notes (2016),
  arXiv:1607.06933

-/

@[expose] public section

open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Sharpness

open StatMech.Ising

/-! ## A. Products of series -/

lemma prod_tsum_fubini {ι : Type*} [DecidableEq ι] (g : ι → ℕ → ℝ)
    (hg : ∀ i, Summable (g i)) (hgnn : ∀ i k, 0 ≤ g i k) (s : Finset ι) :
    Summable (fun m : ↥s → ℕ => ∏ i : ↥s, g i.1 (m i)) ∧
    (∏ i ∈ s, ∑' k : ℕ, g i k)
      = ∑' (m : ↥s → ℕ), ∏ i : ↥s, g i.1 (m i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
    simp only [Finset.prod_empty]
    rw [tsum_eq_single (default : (↥(∅ : Finset ι) → ℕ))]
    · simp
    · intro m hm; exact absurd (Subsingleton.elim m _) hm
  | @insert a s ha IH =>
    obtain ⟨IHsum, IHeq⟩ := IH
    have prodsplit : ∀ m : ↥(insert a s) → ℕ,
        (∏ i : ↥(insert a s), g i.1 (m i))
          = g a (m ⟨a, Finset.mem_insert_self a s⟩) *
            ∏ i : ↥s, g i.1 (m ⟨i.1, Finset.mem_insert_of_mem i.2⟩) := by
      intro m
      rw [← Equiv.prod_comp (Finset.subtypeInsertEquivOption ha).symm
            (fun i : ↥(insert a s) => g i.1 (m i)), Fintype.prod_option]; rfl
    set E : (↥(insert a s) → ℕ) ≃ ℕ × (↥s → ℕ) :=
      (Equiv.arrowCongr (Finset.subtypeInsertEquivOption ha) (Equiv.refl ℕ)).trans
        Equiv.piOptionEquivProd with hE
    have hcomp : ∀ p : ℕ × (↥s → ℕ),
        (fun m : ↥(insert a s) → ℕ => ∏ i : ↥(insert a s), g i.1 (m i)) (E.symm p)
          = g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) := by
      rintro ⟨k, ms⟩
      have happ : ∀ i : ↥(insert a s),
          E.symm (k, ms) i = (Finset.subtypeInsertEquivOption ha i).elim k ms := by
        intro i
        simp only [E, Equiv.symm_trans_apply, Function.comp_apply, Equiv.arrowCongr_symm,
          Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, id_eq,
          Equiv.piOptionEquivProd_symm_apply]
        cases (Finset.subtypeInsertEquivOption ha i) <;> rfl
      simp only
      rw [show (∏ i : ↥(insert a s), g i.1 (E.symm (k, ms) i))
            = ∏ i : ↥(insert a s), g i.1 ((Finset.subtypeInsertEquivOption ha i).elim k ms) from
          Finset.prod_congr rfl (fun i _ => by rw [happ])]
      rw [← Equiv.prod_comp (Finset.subtypeInsertEquivOption ha).symm
            (fun i : ↥(insert a s) => g i.1 ((Finset.subtypeInsertEquivOption ha i).elim k ms)),
        Fintype.prod_option]
      simp only [Equiv.apply_symm_apply, Option.elim]
      have hnone : ((Finset.subtypeInsertEquivOption ha).symm none).1 = a := rfl
      have hsome : ∀ z : ↥s, ((Finset.subtypeInsertEquivOption ha).symm (some z)).1 = z.1 :=
        fun _ => rfl
      rw [hnone]
      exact congrArg _ (Finset.prod_congr rfl (fun z _ => by rw [hsome]))
    clear_value E
    clear hE
    have hjoint : Summable (fun p : ℕ × (↥s → ℕ) => g a p.1 * ∏ i : ↥s, g i.1 (p.2 i)) := by
      apply Summable.mul_of_nonneg (hg a) IHsum
      · intro k; exact hgnn a k
      · intro ms; exact Finset.prod_nonneg (fun i _ => hgnn i.1 _)
    refine ⟨?_, ?_⟩
    · rw [← E.symm.summable_iff]
      have : (fun m => ∏ i : ↥(insert a s), g i.1 (m i)) ∘ E.symm
          = fun p : ℕ × (↥s → ℕ) => g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) := funext hcomp
      rw [this]; exact hjoint
    · rw [Finset.prod_insert ha, IHeq, Summable.tsum_mul_tsum (hg a) IHsum hjoint]
      have hreindex :
          (∑' (m : ↥(insert a s) → ℕ), ∏ i : ↥(insert a s), g i.1 (m i))
            = ∑' (p : ℕ × (↥s → ℕ)), g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) :=
        (E.symm.tsum_eq (fun m => ∏ i : ↥(insert a s), g i.1 (m i))).symm.trans
          (tsum_congr hcomp)
      rw [hreindex]

lemma summable_prod_signed {ι : Type*} [DecidableEq ι] (g : ι → ℕ → ℝ)
    (hgn : ∀ i, Summable (fun k => ‖g i k‖)) (s : Finset ι) :
    Summable (fun m : ↥s → ℕ => ∏ i : ↥s, g i.1 (m i)) := by
  apply Summable.of_norm
  apply ((prod_tsum_fubini (fun i k => ‖g i k‖) hgn (fun i k => norm_nonneg _) s).1).congr
  intro m; rw [norm_prod]

lemma signed_prod_tsum_fubini {ι : Type*} [DecidableEq ι] (g : ι → ℕ → ℝ)
    (hg : ∀ i, Summable (g i)) (hgn : ∀ i, Summable (fun k => ‖g i k‖)) (s : Finset ι) :
    (∏ i ∈ s, ∑' k : ℕ, g i k) = ∑' (m : ↥s → ℕ), ∏ i : ↥s, g i.1 (m i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rw [tsum_eq_single (default : (↥(∅ : Finset ι) → ℕ))]
    · simp
    · intro m hm; exact absurd (Subsingleton.elim m _) hm
  | @insert a s ha IH =>
    have IHsum : Summable (fun m : ↥s → ℕ => ∏ i : ↥s, g i.1 (m i)) :=
      summable_prod_signed g hgn s
    have prodsplit : ∀ m : ↥(insert a s) → ℕ,
        (∏ i : ↥(insert a s), g i.1 (m i))
          = g a (m ⟨a, Finset.mem_insert_self a s⟩) *
            ∏ i : ↥s, g i.1 (m ⟨i.1, Finset.mem_insert_of_mem i.2⟩) := by
      intro m
      rw [← Equiv.prod_comp (Finset.subtypeInsertEquivOption ha).symm
            (fun i : ↥(insert a s) => g i.1 (m i)), Fintype.prod_option]; rfl
    set E : (↥(insert a s) → ℕ) ≃ ℕ × (↥s → ℕ) :=
      (Equiv.arrowCongr (Finset.subtypeInsertEquivOption ha) (Equiv.refl ℕ)).trans
        Equiv.piOptionEquivProd with hE
    have hcomp : ∀ p : ℕ × (↥s → ℕ),
        (fun m : ↥(insert a s) → ℕ => ∏ i : ↥(insert a s), g i.1 (m i)) (E.symm p)
          = g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) := by
      rintro ⟨k, ms⟩
      have happ : ∀ i : ↥(insert a s),
          E.symm (k, ms) i = (Finset.subtypeInsertEquivOption ha i).elim k ms := by
        intro i
        simp only [E, Equiv.symm_trans_apply, Function.comp_apply, Equiv.arrowCongr_symm,
          Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, id_eq,
          Equiv.piOptionEquivProd_symm_apply]
        cases (Finset.subtypeInsertEquivOption ha i) <;> rfl
      simp only
      rw [show (∏ i : ↥(insert a s), g i.1 (E.symm (k, ms) i))
            = ∏ i : ↥(insert a s), g i.1 ((Finset.subtypeInsertEquivOption ha i).elim k ms) from
          Finset.prod_congr rfl (fun i _ => by rw [happ])]
      rw [← Equiv.prod_comp (Finset.subtypeInsertEquivOption ha).symm
            (fun i : ↥(insert a s) => g i.1 ((Finset.subtypeInsertEquivOption ha i).elim k ms)),
        Fintype.prod_option]
      simp only [Equiv.apply_symm_apply, Option.elim]
      have hnone : ((Finset.subtypeInsertEquivOption ha).symm none).1 = a := rfl
      have hsome : ∀ z : ↥s, ((Finset.subtypeInsertEquivOption ha).symm (some z)).1 = z.1 :=
        fun _ => rfl
      rw [hnone]
      exact congrArg _ (Finset.prod_congr rfl (fun z _ => by rw [hsome]))
    clear_value E
    clear hE
    have hjoint : Summable (fun p : ℕ × (↥s → ℕ) => g a p.1 * ∏ i : ↥s, g i.1 (p.2 i)) := by
      have hbase : Summable (fun m : ↥(insert a s) → ℕ => ∏ i : ↥(insert a s), g i.1 (m i)) :=
        summable_prod_signed g hgn (insert a s)
      have := (E.symm.summable_iff
        (f := fun m : ↥(insert a s) → ℕ => ∏ i : ↥(insert a s), g i.1 (m i))).mpr hbase
      refine this.congr (fun p => ?_)
      exact hcomp p
    rw [Finset.prod_insert ha, IH, Summable.tsum_mul_tsum (hg a) IHsum hjoint]
    have hreindex :
        (∑' (m : ↥(insert a s) → ℕ), ∏ i : ↥(insert a s), g i.1 (m i))
          = ∑' (p : ℕ × (↥s → ℕ)), g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) :=
      (E.symm.tsum_eq (fun m => ∏ i : ↥(insert a s), g i.1 (m i))).symm.trans
        (tsum_congr hcomp)
    rw [hreindex]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. Spin sums of monomials -/

lemma sum_spinB_pow (m : ℕ) :
    (∑ b : Bool, (spinB b) ^ m) = if Even m then 2 else 0 := by
  rw [Fintype.sum_bool]
  change (1 : ℝ) ^ m + (-1) ^ m = _
  by_cases hm : Even m
  · rw [ite_eq_left hm, hm.neg_one_pow]; norm_num
  · rw [ite_eq_right hm, Nat.not_even_iff_odd] at *
    rw [hm.neg_one_pow]; norm_num

lemma bond_pow_eq_prod_filter (s : ConfigSpace V) (e : Sym2 V)
    (he : e ∈ G.edgeFinset) (k : ℕ) :
    (bond s e) ^ k = ∏ v ∈ univ.filter (fun v => v ∈ e), (spin s v) ^ k := by
  induction e with
  | h x y =>
    have hadj : G.Adj x y := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he; exact he
    have hxy : x ≠ y := G.ne_of_adj hadj
    rw [bond_mk, mul_pow]
    have hfil : univ.filter (fun v => v ∈ (s(x, y) : Sym2 V)) = {x, y} := by
      ext v; simp [Sym2.mem_iff]
    rw [hfil, Finset.prod_pair hxy]

lemma prod_bond_pow_eq_prod_spin_pow (n : Current V) (s : ConfigSpace V) :
    (∏ e ∈ G.edgeFinset, (bond s e) ^ (n e))
      = ∏ v : V, (spin s v) ^ (incidentFlux G n v) := by
  have hL : (∏ e ∈ G.edgeFinset, (bond s e) ^ (n e))
      = ∏ e ∈ G.edgeFinset, ∏ v ∈ univ.filter (fun v => v ∈ e), (spin s v) ^ (n e) :=
    Finset.prod_congr rfl (fun e he => bond_pow_eq_prod_filter G s e he (n e))
  have hR : (∏ v : V, (spin s v) ^ (incidentFlux G n v))
      = ∏ v : V, ∏ e ∈ G.edgeFinset.filter (fun e => v ∈ e), (spin s v) ^ (n e) := by
    refine Finset.prod_congr rfl (fun v _ => ?_)
    unfold incidentFlux
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hL, hR]
  refine Finset.prod_comm' (s := G.edgeFinset)
    (t := fun e => univ.filter (fun v => v ∈ e))
    (s' := fun v => G.edgeFinset.filter (fun e => v ∈ e)) (t' := univ) ?_
  intro e v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

lemma sum_prod_spin_pow (e : V → ℕ) :
    (∑ s : ConfigSpace V, ∏ v : V, (spin s v) ^ (e v))
      = ∏ v : V, ∑ b : Bool, (spinB b) ^ (e v) := by
  simp_rw [spin_eq_spinB]
  exact (Fintype.prod_sum (fun (v : V) (b : Bool) => (spinB b) ^ (e v))).symm

lemma spinProd_eq_prod_pow (A : Finset V) (s : ConfigSpace V) :
    spinProd A s = ∏ v : V, (spin s v) ^ (if v ∈ A then 1 else 0) := by
  unfold spinProd
  rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ A)
      (fun v => (spin s v) ^ (if v ∈ A then 1 else 0))]
  have h1 : (∏ v ∈ univ.filter (· ∈ A), (spin s v) ^ (if v ∈ A then 1 else 0))
      = ∏ v ∈ A, spin s v := by
    rw [Finset.filter_mem_eq_inter, univ_inter]
    exact Finset.prod_congr rfl (fun v hv => by rw [ite_eq_left hv, pow_one])
  have h2 : (∏ v ∈ univ.filter (¬ · ∈ A), (spin s v) ^ (if v ∈ A then 1 else 0)) = 1 :=
    Finset.prod_eq_one (fun v hv => by
      rw [Finset.mem_filter] at hv; rw [ite_eq_right hv.2, pow_zero])
  rw [h1, h2, mul_one]

lemma spinSum_monomial_eq (A : Finset V) (n : Current V) :
    (∑ s : ConfigSpace V, spinProd A s * ∏ e ∈ G.edgeFinset, (bond s e) ^ (n e))
      = if sources G n = A then (2 : ℝ) ^ (Fintype.card V) else 0 := by
  have hint : ∀ s : ConfigSpace V,
      spinProd A s * ∏ e ∈ G.edgeFinset, (bond s e) ^ (n e)
        = ∏ v : V, (spin s v) ^ (incidentFlux G n v + (if v ∈ A then 1 else 0)) := by
    intro s
    rw [spinProd_eq_prod_pow, prod_bond_pow_eq_prod_spin_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v _ => by rw [pow_add]; ring)
  simp_rw [hint]
  rw [sum_prod_spin_pow]
  simp_rw [sum_spinB_pow]
  by_cases hsrc : sources G n = A
  · rw [ite_eq_left hsrc]
    rw [Finset.prod_congr rfl (g := fun _ => (2 : ℝ)) ?_]
    · rw [Finset.prod_const, Finset.card_univ]
    · intro v _
      rw [ite_eq_left]
      rw [show (if v ∈ A then 1 else 0) = (if v ∈ sources G n then 1 else 0) by rw [hsrc]]
      simp only [mem_sources]
      by_cases hv : Odd (incidentFlux G n v)
      · rw [ite_eq_left hv]; rcases hv with ⟨c, hc⟩; rw [hc]; exact ⟨c + 1, by ring⟩
      · rw [ite_eq_right hv, add_zero]; rw [Nat.not_odd_iff_even] at hv; exact hv
  · rw [ite_eq_right hsrc]
    have hex : ∃ v, ¬ (v ∈ sources G n ↔ v ∈ A) := by
      by_contra h
      push Not at h
      exact hsrc (Finset.ext (fun v => h v))
    obtain ⟨v, hv⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [ite_eq_right]
    rw [mem_sources] at hv
    by_cases hva : v ∈ A
    · rw [ite_eq_left hva]
      simp only [hva, iff_true] at hv
      rw [Nat.not_odd_iff_even] at hv
      rw [Nat.not_even_iff_odd]; rcases hv with ⟨c, hc⟩; rw [hc]; exact ⟨c, by ring⟩
    · rw [ite_eq_right hva, add_zero]
      simp only [hva, iff_false] at hv
      rw [not_not] at hv
      rw [Nat.not_even_iff_odd]; exact hv

/-! ## C. Current sums -/

/-- Extension of a function on the edges of `G` to a current, zero off `E(G)`. -/
noncomputable def ofEdgeFun (m : ↥G.edgeFinset → ℕ) : Current V :=
  fun e => if h : e ∈ G.edgeFinset then m ⟨e, h⟩ else 0

lemma weight_ofEdgeFun (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) :
    weight G β J (ofEdgeFun G m)
      = ∏ e : ↥G.edgeFinset, (β * J e.1) ^ (m e) / (Nat.factorial (m e)) := by
  unfold weight ofEdgeFun
  rw [← Finset.prod_attach G.edgeFinset
      (fun e => (β * J e) ^ (if h : e ∈ G.edgeFinset then m ⟨e, h⟩ else 0)
        / (Nat.factorial (if h : e ∈ G.edgeFinset then m ⟨e, h⟩ else 0)))]
  exact Finset.prod_congr rfl (fun e _ => by rw [dite_eq_left e.2])

lemma prod_bond_pow_ofEdgeFun (s : ConfigSpace V) (m : ↥G.edgeFinset → ℕ) :
    (∏ e ∈ G.edgeFinset, (bond s e) ^ ((ofEdgeFun G m) e))
      = ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
  rw [← Finset.prod_attach G.edgeFinset (fun e => (bond s e) ^ ((ofEdgeFun G m) e))]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold ofEdgeFun; rw [dite_eq_left e.2]

/-- The current sum `Z(∂ = A) = ∑_{∂n = A} w(n)` over currents on the edges of `G`. -/
noncomputable def currentSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  ∑' m : ↥G.edgeFinset → ℕ,
    if sources G (ofEdgeFun G m) = A then weight G β J (ofEdgeFun G m) else 0

/-- The `k`-th term `(βJ_e σ_e)^k / k!` of the expansion of `exp(βJ_e σ_e)`. -/
noncomputable def gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V)
    (e : Sym2 V) (k : ℕ) : ℝ := (β * J e) ^ k * (bond s e) ^ k / k.factorial

omit [Fintype V] [DecidableEq V] in
lemma tsum_gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) (e : Sym2 V) :
    (∑' k, gEdge β J s e k) = Real.exp (β * J e * bond s e) := by
  unfold gEdge
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  exact tsum_congr (fun k => by rw [smul_eq_mul, div_eq_inv_mul, ← mul_pow])

omit [Fintype V] [DecidableEq V] in
lemma summable_gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) (e : Sym2 V) :
    Summable (gEdge β J s e) := by
  unfold gEdge
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (β * J e * bond s e)
  convert h using 2 with k; rw [smul_eq_mul, div_eq_inv_mul, ← mul_pow]

omit [Fintype V] [DecidableEq V] in
lemma summable_norm_gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) (e : Sym2 V) :
    Summable (fun k => ‖gEdge β J s e k‖) := by
  unfold gEdge
  have h2 : Summable (fun k : ℕ => (|β * J e * bond s e|) ^ k / k.factorial) := by
    have := NormedSpace.expSeries_summable' (𝕂 := ℝ) (|β * J e * bond s e|)
    convert this using 2 with k; rw [smul_eq_mul, div_eq_inv_mul]
  refine h2.congr (fun k => ?_)
  rw [Real.norm_eq_abs, abs_div, ← mul_pow, abs_pow]
  congr 1
  exact (abs_of_nonneg (by positivity)).symm

lemma prod_gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) (m : ↥G.edgeFinset → ℕ) :
    (∏ e : ↥G.edgeFinset, gEdge β J s e.1 (m e))
      = weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
  rw [weight_ofEdgeFun, ← Finset.prod_mul_distrib]
  unfold gEdge
  exact Finset.prod_congr rfl (fun e _ => by ring)

/-! ## D. The representation -/

/-- The Boltzmann weight `exp(β ∑_e J_e σ_e)` with couplings `J`. -/
noncomputable def boltzmannJ (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (β * ∑ e ∈ G.edgeFinset, J e * bond s e)

lemma boltzmannJ_eq_tsum (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) :
    boltzmannJ G β J s
      = ∑' m : ↥G.edgeFinset → ℕ,
          weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
  have hprod : boltzmannJ G β J s = ∏ e ∈ G.edgeFinset, ∑' k, gEdge β J s e k := by
    unfold boltzmannJ
    rw [show (β * ∑ e ∈ G.edgeFinset, J e * bond s e)
          = ∑ e ∈ G.edgeFinset, β * (J e * bond s e) by rw [Finset.mul_sum]]
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl (fun e _ => by rw [tsum_gEdge]; congr 1; ring)
  rw [hprod,
    signed_prod_tsum_fubini (gEdge β J s)
      (fun e => summable_gEdge β J s e) (fun e => summable_norm_gEdge β J s e) G.edgeFinset]
  exact tsum_congr (fun m => prod_gEdge G β J s m)

lemma summable_weight_bond (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)) := by
  have h := summable_prod_signed (gEdge β J s) (fun e => summable_norm_gEdge β J s e) G.edgeFinset
  exact h.congr (fun m => prod_gEdge G β J s m)

lemma spinSum_eq_currentSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    (∑ s : ConfigSpace V, spinProd A s * boltzmannJ G β J s)
      = (2 : ℝ) ^ (Fintype.card V) * currentSum G β J A := by
  classical
  have hstep1 : ∀ s : ConfigSpace V,
      spinProd A s * boltzmannJ G β J s
        = ∑' m : ↥G.edgeFinset → ℕ,
            weight G β J (ofEdgeFun G m)
              * (spinProd A s * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)) := by
    intro s
    rw [boltzmannJ_eq_tsum, ← tsum_mul_left]
    refine tsum_congr (fun m => ?_); ring
  simp_rw [hstep1]
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (ConfigSpace V)))
    (f := fun s (m : ↥G.edgeFinset → ℕ) =>
      weight G β J (ofEdgeFun G m)
        * (spinProd A s * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)))
    (fun s _ => by
      have h := (summable_weight_bond G β J s).mul_left (spinProd A s)
      refine h.congr (fun m => ?_)
      ring)]
  have hinner : ∀ m : ↥G.edgeFinset → ℕ,
      (∑ s : ConfigSpace V,
          weight G β J (ofEdgeFun G m)
            * (spinProd A s * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)))
        = if sources G (ofEdgeFun G m) = A
            then weight G β J (ofEdgeFun G m) * (2 : ℝ) ^ (Fintype.card V) else 0 := by
    intro m
    rw [← Finset.mul_sum]
    have hspin : (∑ s : ConfigSpace V,
          spinProd A s * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e))
        = if sources G (ofEdgeFun G m) = A then (2 : ℝ) ^ (Fintype.card V) else 0 := by
      have hbond : ∀ s : ConfigSpace V,
          (∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e))
            = ∏ e ∈ G.edgeFinset, (bond s e) ^ ((ofEdgeFun G m) e) :=
        fun s => (prod_bond_pow_ofEdgeFun G s m).symm
      simp_rw [hbond]
      exact spinSum_monomial_eq G A (ofEdgeFun G m)
    rw [hspin]
    by_cases h : sources G (ofEdgeFun G m) = A <;> simp [h]
  simp_rw [hinner]
  unfold currentSum
  rw [mul_comm ((2 : ℝ) ^ (Fintype.card V)), ← tsum_mul_right]
  refine tsum_congr (fun m => ?_)
  by_cases h : sources G (ofEdgeFun G m) = A <;> simp [h]

/-- The partition function with couplings `J`. -/
noncomputable def partitionJ (β : ℝ) (J : Sym2 V → ℝ) : ℝ :=
  ∑ s : ConfigSpace V, boltzmannJ G β J s

/-- The correlation `⟨σ_A⟩_{β,J}` with couplings `J`. -/
noncomputable def expectationJ (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  (∑ s : ConfigSpace V, spinProd A s * boltzmannJ G β J s) / partitionJ G β J

omit [DecidableEq V] in
lemma boltzmannJ_pos (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) :
    0 < boltzmannJ G β J s := Real.exp_pos _

lemma partitionJ_pos (β : ℝ) (J : Sym2 V → ℝ) : 0 < partitionJ G β J :=
  Finset.sum_pos (fun s _ => boltzmannJ_pos G β J s) Finset.univ_nonempty

lemma partitionJ_eq_currentSum (β : ℝ) (J : Sym2 V → ℝ) :
    partitionJ G β J = (2 : ℝ) ^ (Fintype.card V) * currentSum G β J ∅ := by
  unfold partitionJ
  rw [show (∑ s : ConfigSpace V, boltzmannJ G β J s)
        = ∑ s : ConfigSpace V, spinProd (∅ : Finset V) s * boltzmannJ G β J s from
      Finset.sum_congr rfl (fun s _ => by rw [spinProd_empty, one_mul])]
  exact spinSum_eq_currentSum G β J ∅

/-- The random-current representation: `⟨σ_A⟩_{β,J} = Z(∂ = A)/Z(∂ = ∅)`. Reference: M. Aizenman,
"Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48; J. Ginibre
(1970); H. Duminil-Copin, "Random currents expansion of the Ising model", lecture notes (2016),
arXiv:1607.06933. -/
theorem current_representation (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    expectationJ G β J A = currentSum G β J A / currentSum G β J ∅ := by
  unfold expectationJ
  rw [spinSum_eq_currentSum, partitionJ_eq_currentSum]
  have h2 : (2 : ℝ) ^ (Fintype.card V) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ h2]

omit [DecidableEq V] in
lemma boltzmannJ_one_eq_isingWeight (β : ℝ) (s : ConfigSpace V) :
    boltzmannJ G β (fun _ => 1) s = isingWeight G β 0 s := by
  unfold boltzmannJ isingWeight hamiltonian
  congr 1
  simp only [zero_mul, sub_zero, one_mul]
  ring

lemma partitionJ_one_eq_isingZ (β : ℝ) :
    partitionJ G β (fun _ => 1) = isingZ G β 0 := by
  unfold partitionJ isingZ
  exact Finset.sum_congr rfl (fun s _ => boltzmannJ_one_eq_isingWeight G β s)

lemma expectationJ_one_eq_isingExpectation (β : ℝ) (A : Finset V) :
    expectationJ G β (fun _ => 1) A = isingExpectation G β 0 (spinProd A) := by
  unfold expectationJ isingExpectation isingProb
  rw [partitionJ_one_eq_isingZ, Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [boltzmannJ_one_eq_isingWeight, div_mul_eq_mul_div, mul_comm]

lemma isingExpectation_eq_currentSum_ratio (β : ℝ) (A : Finset V) :
    isingExpectation G β 0 (spinProd A)
      = currentSum G β (fun _ => 1) A / currentSum G β (fun _ => 1) ∅ := by
  rw [← expectationJ_one_eq_isingExpectation, current_representation]

end Sharpness

end StatMech
