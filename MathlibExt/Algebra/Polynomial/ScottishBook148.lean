/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

/-!
# Auerbach's problem on zero sets of real polynomials

A nonzero real polynomial has connected nonvanishing set exactly when all its
irreducible factors are sign definite.
-/

namespace MathlibExt.Algebra.Polynomial.ScottishBook148Wanted

open Filter MvPolynomial Set
open scoped BigOperators _root_.Polynomial Topology

private theorem dense_nonvanishing {σ : Type*} [Finite σ] {p : MvPolynomial σ ℝ}
    (hp : p ≠ 0) : Dense {x : σ → ℝ | eval x p ≠ 0} := by
  let := Fintype.ofFinite σ
  refine dense_iff_inter_open.mpr fun U hU ⟨x, hx⟩ ↦ ?_
  by_contra h
  apply hp
  have hzero : (fun y ↦ eval y p) =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    by_contra hy'
    exact h ⟨y, hy, hy'⟩
  have heq := (AnalyticOnNhd.eval_mvPolynomial p).eq_of_eventuallyEq analyticOnNhd_const hzero
  exact MvPolynomial.funext fun y ↦ by simpa using congrFun heq y

private theorem derivative_eval_eq_zero_of_sign {f : ℝ[X]} {t : ℝ}
    (h : (∀ s : ℝ, 0 ≤ f.eval s) ∨ ∀ s : ℝ, f.eval s ≤ 0) (ht : f.eval t = 0) :
    f.derivative.eval t = 0 := by
  rw [← (f.hasDerivAt t).deriv]
  rcases h with h | h
  · have hm : IsMinOn f.eval univ t := isMinOn_univ_iff.mpr (by simpa only [ht] using h)
    exact (hm.isLocalMin univ_mem).deriv_eq_zero
  · have hm : IsMaxOn f.eval univ t := isMaxOn_univ_iff.mpr (by simpa only [ht] using h)
    exact (hm.isLocalMax univ_mem).deriv_eq_zero

/-- Away from the zero set of an exceptional polynomial, the distinguished variable
can take any real value without yielding a zero. -/
private theorem exists_exceptional_of_irreducible {σ : Type*}
    {Q : MvPolynomial (Option σ) ℝ} (hQ : Irreducible Q)
    (hs : (∀ x : Option σ → ℝ, 0 ≤ eval x Q) ∨ ∀ x : Option σ → ℝ, eval x Q ≤ 0) :
    ∃ E : MvPolynomial σ ℝ, E ≠ 0 ∧
      ∀ x : σ → ℝ, eval x E ≠ 0 → ∀ t : ℝ, eval (fun i ↦ i.elim t x) Q ≠ 0 := by
  let A := MvPolynomial σ ℝ
  let f : A[X] := optionEquivLeft ℝ σ Q
  have hf : Irreducible f := hQ.map (optionEquivLeft ℝ σ).toMulEquiv
  by_cases hd : f.natDegree = 0
  · refine ⟨f.coeff 0, ?_, fun x hx t ↦ ?_⟩
    · intro hz
      exact hf.ne_zero (by rw [Polynomial.eq_C_of_natDegree_eq_zero hd, hz, Polynomial.C_0])
    · rw [optionEquivLeft_elim_eval]
      change (f.map (eval x)).eval t ≠ 0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.map_C, Polynomial.eval_C]
      exact hx
  -- Over the fraction field, Gauss's lemma gives an irreducible and hence separable polynomial.
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  have hφ : Function.Injective φ := IsFractionRing.injective A K
  let : CharZero A :=
    (RingHom.charZero_iff (ϕ := (C : ℝ →+* A)) (C_injective σ ℝ)).mp inferInstance
  let : CharZero K := (RingHom.charZero_iff hφ).mp inferInstance
  have hprim : f.IsPrimitive := by
    refine Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr fun a ⟨g, hg⟩ ↦ ?_
    rcases hf.isUnit_or_isUnit hg with hu | hu
    · exact Polynomial.isUnit_C.mp hu
    · apply (hd ?_).elim
      rw [hg, Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu),
        ← Polynomial.C_mul, Polynomial.natDegree_C]
  have hirr : Irreducible (f.map φ) :=
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hprim).mp hf
  let R := f.resultant f.derivative
  have hR : R ≠ 0 := by
    have h := Polynomial.resultant_ne_zero _ _ hirr.separable
    rw [Polynomial.derivative_map, Polynomial.natDegree_map_eq_of_injective hφ,
      Polynomial.natDegree_map_eq_of_injective hφ, Polynomial.resultant_map_map] at h
    intro hz
    apply h
    change φ R = 0
    rw [hz, map_zero]
  -- The leading coefficient keeps both degrees fixed when we specialize the coefficients.
  refine ⟨f.leadingCoeff * R, mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf.ne_zero) hR,
    fun x hx t ↦ ?_⟩
  let g := f.map (eval x)
  have hx' : eval x f.leadingCoeff * eval x R ≠ 0 := by simpa only [map_mul] using hx
  have hlead : eval x f.leadingCoeff ≠ 0 := (mul_ne_zero_iff.mp hx').1
  have hg : g.natDegree = f.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero (eval x) hlead
  have hg' : (f.derivative.map (eval x)).natDegree = f.derivative.natDegree := by
    refine le_antisymm Polynomial.natDegree_map_le ?_
    rw [← Polynomial.derivative_map, Polynomial.natDegree_derivative (f.map (eval x)),
      show (f.map (eval x)).natDegree = f.natDegree from hg]
    exact Polynomial.natDegree_derivative_le f
  have hres : g.resultant g.derivative ≠ 0 := by
    change (f.map (eval x)).resultant (f.map (eval x)).derivative ≠ 0
    rw [Polynomial.derivative_map, show (f.map (eval x)).natDegree = f.natDegree from hg,
      hg', Polynomial.resultant_map_map]
    exact (mul_ne_zero_iff.mp hx').2
  have hcop : IsCoprime g g.derivative := by
    by_contra hc
    exact hres (Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl (fun hz ↦ hd (by simpa [hz] using hg.symm)), hc⟩)
  have hsign : (∀ s : ℝ, 0 ≤ g.eval s) ∨ ∀ s : ℝ, g.eval s ≤ 0 := by
    rcases hs with hs | hs
    · exact Or.inl fun s ↦ (optionEquivLeft_elim_eval ℝ σ x s Q) ▸ hs _
    · exact Or.inr fun s ↦ (optionEquivLeft_elim_eval ℝ σ x s Q) ▸ hs _
  rw [optionEquivLeft_elim_eval]
  intro ht
  change g.eval t = 0 at ht
  have ht' := derivative_eval_eq_zero_of_sign hsign ht
  simpa [Polynomial.aeval_def, ht, ht'] using Polynomial.aeval_ne_zero_of_isCoprime hcop t

private theorem exists_exceptional {σ : Type*} (P : MvPolynomial (Option σ) ℝ)
    (hP : P ≠ 0)
    (h : ∀ Q : MvPolynomial (Option σ) ℝ, Irreducible Q → Q ∣ P →
      (∀ x, 0 ≤ eval x Q) ∨ ∀ x, eval x Q ≤ 0) :
    ∃ E : MvPolynomial σ ℝ, E ≠ 0 ∧
      ∀ x : σ → ℝ, eval x E ≠ 0 → ∀ t : ℝ, eval (fun i ↦ i.elim t x) P ≠ 0 := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hP rfl).elim
  | unit P hunit =>
    refine ⟨1, one_ne_zero, fun x _ t ↦ ?_⟩
    exact (hunit.map (eval fun i : Option σ ↦ i.elim t x)).ne_zero
  | mul P Q hP₀ hQ ih =>
    obtain ⟨E, hE, he⟩ := ih hP₀ fun Q' hQ' hd ↦ h Q' hQ' (hd.trans (dvd_mul_left P Q))
    obtain ⟨F, hF, hf⟩ := exists_exceptional_of_irreducible hQ (h Q hQ (dvd_mul_right Q P))
    refine ⟨E * F, mul_ne_zero hE hF, fun x hx t ↦ ?_⟩
    rw [map_mul] at hx ⊢
    exact mul_ne_zero (hf x (mul_ne_zero_iff.mp hx).2 t) (he x (mul_ne_zero_iff.mp hx).1 t)

private theorem exists_exceptional_update {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P ≠ 0)
    (h : ∀ Q : MvPolynomial (Fin n) ℝ, Irreducible Q → Q ∣ P →
      (∀ x, 0 ≤ eval x Q) ∨ ∀ x, eval x Q ≤ 0) (i : Fin n) :
    ∃ E : MvPolynomial {j : Fin n // j ≠ i} ℝ, E ≠ 0 ∧
      ∀ x : Fin n → ℝ, eval (x ∘ Subtype.val) E ≠ 0 →
        ∀ t : ℝ, eval (Function.update x i t) P ≠ 0 := by
  classical
  let e := renameEquiv ℝ (Equiv.optionSubtypeNe i).symm
  have hsign : ∀ Q, Irreducible Q → Q ∣ e P →
      (∀ x, 0 ≤ eval x Q) ∨ ∀ x, eval x Q ≤ 0 := by
    intro Q hQ hd
    have hd' : e.symm Q ∣ P := by simpa using map_dvd e.symm hd
    have h' := h _ (hQ.map e.symm.toMulEquiv) hd'
    have he (x : Option {j : Fin n // j ≠ i} → ℝ) :
        eval (x ∘ (Equiv.optionSubtypeNe i).symm) (e.symm Q) = eval x Q := by
      rw [← eval_rename]
      change eval x (e (e.symm Q)) = eval x Q
      rw [AlgEquiv.apply_symm_apply]
    exact h'.imp (fun hl x ↦ he x ▸ hl _) (fun hr x ↦ he x ▸ hr _)
  obtain ⟨E, hE, he⟩ := exists_exceptional (e P) (e.injective.ne (by simpa using hP)) hsign
  refine ⟨E, hE, fun x hx t ↦ ?_⟩
  have heval : (fun j : Option {j : Fin n // j ≠ i} ↦ j.elim t (x ∘ Subtype.val)) ∘
      (Equiv.optionSubtypeNe i).symm = Function.update x i t := by
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Equiv.optionSubtypeNe_symm_of_ne hj, Function.update_of_ne hj]
  simpa only [e, renameEquiv_apply, eval_rename, heval] using he _ hx t

/-- Choose the two endpoints jointly so that every line in their coordinate-by-coordinate
chain avoids the zero set. -/
private theorem isConnected_of_exceptional_update {n : ℕ} {P : MvPolynomial (Fin n) ℝ}
    (hP : P ≠ 0)
    (h : ∀ i : Fin n, ∃ E : MvPolynomial {j : Fin n // j ≠ i} ℝ, E ≠ 0 ∧
      ∀ x : Fin n → ℝ, eval (x ∘ Subtype.val) E ≠ 0 →
        ∀ t : ℝ, eval (Function.update x i t) P ≠ 0) :
    IsConnected {x : Fin n → ℝ | eval x P ≠ 0} := by
  classical
  let S : Set (Fin n → ℝ) := {x | eval x P ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun (continuous_eval P) continuous_const
  refine ⟨(dense_nonvanishing hP).nonempty, ?_⟩
  change IsPreconnected S
  intro U V hU hV hUV hSU hSV
  by_contra hdisj
  obtain ⟨a, haS, haU⟩ := hSU
  obtain ⟨b, hbS, hbV⟩ := hSV
  choose E hE hline using h
  let pick (k : ℕ) (j : Fin n) : Fin n ⊕ Fin n :=
    if (j : ℕ) < k then Sum.inr j else Sum.inl j
  let lift (i : Fin n) (j : {j : Fin n // j ≠ i}) := pick i j.val
  have hlift (i : Fin n) : Function.Injective (lift i) := by
    intro j k hjk
    apply Subtype.ext
    simpa [lift, pick, apply_ite (Sum.elim id id)] using congrArg (Sum.elim id id) hjk
  -- Each renamed polynomial tests one line of the chain as a function of the two endpoints.
  let F := ∏ i : Fin n, rename (lift i) (E i)
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦
    fun hzero ↦ hE i ((rename_injective _ (hlift i)) (by simpa using hzero))
  let L (z : Fin n ⊕ Fin n → ℝ) (j : Fin n) := z (Sum.inl j)
  let R (z : Fin n ⊕ Fin n → ℝ) (j : Fin n) := z (Sum.inr j)
  have hL : Continuous L := continuous_pi fun j ↦ continuous_apply (Sum.inl j)
  have hR : Continuous R := continuous_pi fun j ↦ continuous_apply (Sum.inr j)
  obtain ⟨z, hz, hzL, hzR⟩ := (dense_nonvanishing hF).exists_mem_open
    (((hS.inter hU).preimage hL).inter ((hS.inter hV).preimage hR))
    ⟨Sum.elim a b, ⟨haS, haU⟩, ⟨hbS, hbV⟩⟩
  have hzE (i : Fin n) : eval (z ∘ lift i) (E i) ≠ 0 := by
    change eval z (∏ i : Fin n, rename (lift i) (E i)) ≠ 0 at hz
    rw [← eval_rename]
    rw [map_prod] at hz
    exact Finset.prod_ne_zero_iff.mp hz i (Finset.mem_univ i)
  let w (k : ℕ) (j : Fin n) := z (pick k j)
  have hw₀ : w 0 = L z := by
    funext j
    simp [w, pick, L]
  have hwn : w n = R z := by
    funext j
    simp [w, pick, R, j.isLt]
  have hstep (i : Fin n) : w i ∈ U → w (i + 1 : ℕ) ∈ U := by
    intro hi
    let line (t : ℝ) := Function.update (w i) i t
    have hsub : range line ⊆ S := by
      rintro _ ⟨t, rfl⟩
      exact hline i (w i) (hzE i) t
    have hconn : IsPreconnected (range line) := by
      have hc : Continuous line := (continuous_const (y := w i)).update i continuous_id
      rw [← image_univ]
      exact isPreconnected_univ.image _ hc.continuousOn
    have hstart : w i ∈ range line :=
      ⟨w i i, Function.update_eq_self i (w i)⟩
    have hend : w (i + 1 : ℕ) ∈ range line := by
      refine ⟨z (Sum.inr i), ?_⟩
      funext j
      by_cases hj : j = i
      · subst j
        simp [line, w, pick]
      · have hlt : ((j : ℕ) < (i : ℕ) + 1) ↔ (j : ℕ) < (i : ℕ) := by
          have hne : (j : ℕ) ≠ (i : ℕ) := fun hji ↦ hj (Fin.ext hji)
          omega
        simp [line, Function.update_of_ne hj, w, pick, hlt]
    rcases isPreconnected_iff_subset_of_disjoint.mp hconn U V hU hV
      (hsub.trans hUV) (not_nonempty_iff_eq_empty.mp fun h ↦
        hdisj (h.mono (inter_subset_inter_left _ hsub))) with hU' | hV'
    · exact hU' hend
    · exact (hdisj ⟨w i, hsub hstart, hi, hV' hstart⟩).elim
  have hwU (k : ℕ) (hk : k ≤ n) : w k ∈ U := by
    induction k with
    | zero => exact hw₀ ▸ hzL.2
    | succ k ih =>
      exact hstep ⟨k, Nat.lt_of_succ_le hk⟩ (ih (Nat.le_of_succ_le hk))
  exact hdisj ⟨R z, hzR.1, hwn ▸ hwU n le_rfl, hzR.2⟩

public section

/--
Let `P` be a nonzero real polynomial in `n` variables. Its zero set does
not cut (separate) Euclidean space, i.e. the complement of the zero set is
connected, if and only if every irreducible factor of `P` over the reals is
always nonnegative or always nonpositive (as a function). The complement of
a real algebraic hypersurface is semialgebraic, so connectedness of the
complement is equivalent to the path-connectedness used by Rojas.
Source: H. Auerbach, Problem 148 of the Scottish Book; both necessity and
sufficiency proved by J. M. Rojas, "About Herman Auerbach's problem on
factors of real polynomials with connected zero set complement", 2015 (see
the commentary in Mauldin (ed.), The Scottish Book, 2nd ed., 2015).
-/
theorem auerbachPolynomialZeroSetSeparatesIffFactorsSignDefinite :
    ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ), P ≠ 0 →
      (IsConnected {x : Fin n → ℝ | (MvPolynomial.eval x) P ≠ 0} ↔
        ∀ Q : MvPolynomial (Fin n) ℝ, Irreducible Q → Q ∣ P →
          (∀ x : Fin n → ℝ, 0 ≤ (MvPolynomial.eval x) Q) ∨
            ∀ x : Fin n → ℝ, (MvPolynomial.eval x) Q ≤ 0) := by
  intro n P hP
  constructor
  · intro hconn Q _ hQP
    by_contra! hsign
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hsign
    have hd := dense_nonvanishing hP
    obtain ⟨x, hxP, hx⟩ := hd.exists_mem_open
      (isOpen_lt (continuous_eval Q) continuous_const) ⟨a, ha⟩
    obtain ⟨y, hyP, hy⟩ := hd.exists_mem_open
      (isOpen_lt continuous_const (continuous_eval Q)) ⟨b, hb⟩
    change eval x Q < 0 at hx
    change 0 < eval y Q at hy
    have himage := hconn.2.image (fun z ↦ eval z Q) (continuous_eval Q).continuousOn
    have hinterval := himage.ordConnected
    obtain ⟨z, hzP, hzQ⟩ :=
      hinterval.out (mem_image_of_mem _ hxP) (mem_image_of_mem _ hyP) ⟨hx.le, hy.le⟩
    change eval z Q = 0 at hzQ
    obtain ⟨T, rfl⟩ := hQP
    exact hzP (by rw [map_mul, hzQ, zero_mul])
  · intro h
    exact isConnected_of_exceptional_update hP (exists_exceptional_update P hP h)

end

end MathlibExt.Algebra.Polynomial.ScottishBook148Wanted
