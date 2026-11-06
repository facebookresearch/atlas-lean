/-
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0.

Adapted from Fermat's Last Theorem in Lean 4, revision
6e837e75355538c7f80bab5b956861e86c4eacc2:
P2M/Sol/
S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.lean
and its theorem wrapper. The published source names no individual author.
The repository NOTICE credits Mathlib and its respective authors for library
material. The canonical recurrence adapters below are new; source proof
bookkeeping is private, with canonical LinearRecurrence solution spaces.
-/
module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Data.Int.Interval

/-!
# Positive weighted line sums of recurrent sequences

The public result preserves integer lower supports, nonzero geometric twists,
and the separated recurrence outside a box (an OR condition). Its proof uses
finite-dimensional shift spaces, not analytic convergence or zero-set theory.
-/

open scoped BigOperators

noncomputable section

namespace Polynomial

private def backwardRecurrence (D : Polynomial ℂ) (K : ℕ) :
    LinearRecurrence ℂ where
  order := K
  coeffs i := -(D.coeff 0)⁻¹ * D.coeff (K - i)

private theorem backward_sum (D : Polynomial ℂ) (K : ℕ)
    (hK : D.natDegree ≤ K) (f : ℕ → ℂ) :
    ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * f i =
      D.coeff 0 * f 0 + ∑ i : Fin K, D.coeff (K - i) * f (K - i) := by
  classical
  have hp : ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * f i =
      ∑ i ∈ Finset.range (K + 1), D.coeff i * f i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i _ hi
    rw [coeff_eq_zero_of_natDegree_lt, zero_mul]
    simp only [Finset.mem_range, not_lt] at hi
    omega
  rw [hp, ← Finset.sum_range_reflect, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self]
  rw [add_comm]
  congr 1
  exact Finset.sum_range _

/-- An eventual backward recurrence gives an all-index solution on the
explicit tail starting at `N + M`. The order-zero case is included. -/
public theorem exists_isSolution_tail (x : ℤ → ℂ) (N : ℤ)
    (D : Polynomial ℂ) (M : ℕ) (hD : D.eval 0 ≠ 0)
    (hrec : ∀ m : ℕ, M ≤ m →
      ∑ i ∈ Finset.range (D.natDegree + 1),
        D.coeff i * x (N + (m : ℤ) - (i : ℤ)) = 0) :
    ∃ E : LinearRecurrence ℂ, E.order = D.natDegree ∧
      E.IsSolution (fun n => x (N + (M : ℤ) + (n : ℤ))) := by
  classical
  refine ⟨backwardRecurrence D D.natDegree, rfl, ?_⟩
  intro n
  change x (N + (M : ℤ) + ((n + D.natDegree : ℕ) : ℤ)) =
    ∑ i : Fin D.natDegree, (-(D.coeff 0)⁻¹ *
      D.coeff (D.natDegree - i)) * x (N + M + ((n + i : ℕ) : ℤ))
  have h := hrec (M + n + D.natDegree) (by omega)
  rw [backward_sum D D.natDegree le_rfl] at h
  have hi (i : Fin D.natDegree) :
      N + ((M + n + D.natDegree : ℕ) : ℤ) -
        ((D.natDegree - i : ℕ) : ℤ) = N + M + ((n + i : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub i.isLt.le]
    ring
  simp_rw [hi] at h
  simp only [Nat.cast_zero, sub_zero, Nat.cast_add, add_assoc] at h ⊢
  have hD0 : D.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  rw [← mul_right_inj' hD0, Finset.mul_sum]
  simp only [← mul_assoc, mul_neg, mul_inv_cancel₀ hD0, neg_one_mul]
  simp only [neg_mul, Finset.sum_neg_distrib]
  linear_combination h

private theorem isSolution_iff_backward (D : Polynomial ℂ)
    (hD : D.eval 0 ≠ 0) (K : ℕ) (hK : D.natDegree ≤ K)
    (s : ℕ → ℂ) :
    (backwardRecurrence D K).IsSolution s ↔
      ∀ m, K ≤ m → ∑ i ∈ Finset.range (D.natDegree + 1),
        D.coeff i * s (m - i) = 0 := by
  classical
  have hD0 : D.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  have key (n : ℕ) :
      s (n + K) = ∑ i : Fin K, (-(D.coeff 0)⁻¹ * D.coeff (K - i)) *
        s (n + i) ↔
      ∑ i ∈ Finset.range (D.natDegree + 1),
        D.coeff i * s (n + K - i) = 0 := by
    rw [backward_sum D K hK]
    have hi (i : Fin K) : n + K - (K - i) = n + i := by omega
    simp_rw [hi]
    simp only [Nat.sub_zero]
    rw [← mul_right_inj' hD0, Finset.mul_sum]
    simp only [← mul_assoc, mul_neg, mul_inv_cancel₀ hD0,
      neg_mul, one_mul, Finset.sum_neg_distrib]
    constructor <;> intro h <;> linear_combination h
  constructor
  · intro hs m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + K := ⟨m - K, by omega⟩
    exact (key n).mp (hs n)
  · intro hs n
    exact (key n).mpr (hs (n + K) (by omega))

private def sh (k : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f n := f (n + k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] private theorem sh_apply (k : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    sh k f n = f (n + k) := rfl

private theorem sh_zero (f : ℕ → ℂ) : sh 0 f = f := by
  funext n
  simp

private theorem sh_sh (j k : ℕ) (f : ℕ → ℂ) :
    sh j (sh k f) = sh (k + j) f := by
  funext n
  simp [add_assoc, add_comm j k]

private theorem sh_one_sh (k : ℕ) (f : ℕ → ℂ) :
    sh 1 (sh k f) = sh (k + 1) f := sh_sh 1 k f

private def ShiftFinite (s : ℕ → ℂ) : Prop :=
  ∃ W : Submodule ℂ (ℕ → ℂ), FiniteDimensional ℂ W ∧
    (∀ f ∈ W, sh 1 f ∈ W) ∧ ∃ K : ℕ, ∀ k, K ≤ k → sh k s ∈ W

private theorem shiftFinite_of_isSolution (E : LinearRecurrence ℂ)
    (s : ℕ → ℂ) (hs : E.IsSolution s) : ShiftFinite s := by
  have hW : ∀ f ∈ E.solSpace, sh 1 f ∈ E.solSpace := by
    intro f hf n
    simpa only [sh_apply, Nat.add_right_comm] using hf (n + 1)
  have hsh : ∀ k, sh k s ∈ E.solSpace := by
    intro k
    induction k with
    | zero => rwa [sh_zero]
    | succ k ih => rw [← sh_one_sh]; exact hW _ ih
  refine ⟨E.solSpace, ?_, hW, 0, fun k _ => hsh k⟩
  exact FiniteDimensional.of_injective E.toInit.toLinearMap E.toInit.injective

private theorem shiftFinite_of_eventually {s s' : ℕ → ℂ}
    (hs : ShiftFinite s) (a b K₀ : ℕ)
    (h : ∀ k, K₀ ≤ k → sh (k + a) s' = sh (k + b) s) :
    ShiftFinite s' := by
  obtain ⟨W, hfd, hW, K, hK⟩ := hs
  refine ⟨W, hfd, hW, K₀ + K + a, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + a := ⟨k - a, by omega⟩
  rw [h j (by omega)]
  exact hK _ (by omega)

private def SR (x : ℤ → ℂ) : Prop :=
  ∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧
    (∀ m : ℤ, m < N → x m = 0) ∧
    (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
      E.coeff i * x (N + (m : ℤ) - (i : ℤ)) = 0)

private def seqAt (x : ℤ → ℂ) (N : ℤ) : ℕ → ℂ := fun m => x (N + m)

@[simp] private theorem seqAt_apply (x : ℤ → ℂ) (N : ℤ) (m : ℕ) :
    seqAt x N m = x (N + m) := rfl

private theorem shiftFinite_of_rec (x : ℤ → ℂ) (N : ℤ)
    (D : Polynomial ℂ) (M : ℕ) (hD : D.eval 0 ≠ 0)
    (hrec : ∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (D.natDegree + 1),
      D.coeff i * x (N + (m : ℤ) - (i : ℤ)) = 0) :
    ShiftFinite (seqAt x N) := by
  obtain ⟨E, _, hs⟩ := exists_isSolution_tail x N D M hD hrec
  refine shiftFinite_of_eventually (shiftFinite_of_isSolution E _ hs)
    M 0 0 fun k _ => ?_
  funext n
  simp only [sh_apply, seqAt_apply, Nat.cast_add, add_zero]
  congr 1
  ring

private theorem sr_of_shiftFinite (x : ℤ → ℂ) (N : ℤ)
    (hN : ∀ m : ℤ, m < N → x m = 0)
    (hsf : ShiftFinite (seqAt x N)) : SR x := by
  classical
  obtain ⟨W, hfd, hW, K, hK⟩ := hsf
  have := hfd
  let T : W →ₗ[ℂ] W := (sh 1).restrict (fun f hf => hW f hf)
  have hTpow : ∀ (j : ℕ) (w : W),
      ((T ^ j) w : ℕ → ℂ) = sh j (w : ℕ → ℂ) := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, Module.End.one_apply, sh_zero]
    | succ j ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih,
        show ((T w : W) : ℕ → ℂ) = sh 1 (w : ℕ → ℂ) from rfl,
        sh_sh, add_comm]
  let p := T.charpoly
  have hp : Polynomial.aeval T p = 0 := LinearMap.aeval_self_charpoly T
  set r := p.natDegree with hr
  have hmonic : p.Monic := LinearMap.charpoly_monic T
  let E := p.reverse
  have hE0 : E.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, hmonic.leadingCoeff]
    exact one_ne_zero
  refine ⟨N, E, K + r, hE0, hN, fun m hm => ?_⟩
  have hdeg : E.natDegree ≤ r := reverse_natDegree_le p
  have hsum : ∑ i ∈ Finset.range (E.natDegree + 1),
      E.coeff i * x (N + (m : ℤ) - (i : ℤ)) =
      ∑ i ∈ Finset.range (r + 1),
        E.coeff i * x (N + (m : ℤ) - (i : ℤ)) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i _ hi
    rw [coeff_eq_zero_of_natDegree_lt, zero_mul]
    simp only [Finset.mem_range, not_lt] at hi
    omega
  rw [hsum]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + r := ⟨m - r, by omega⟩
  have hk : K ≤ k := by omega
  have e1 : ∀ i ∈ Finset.range (r + 1),
      E.coeff i * x (N + ((k + r : ℕ) : ℤ) - (i : ℤ)) =
        p.coeff (r - i) * seqAt x N (k + (r - i)) := by
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [coeff_reverse, revAt_le (by rw [← hr]; exact hi'), seqAt_apply]
    congr 2
    push_cast
    omega
  rw [Finset.sum_congr rfl e1]
  have hrefl := Finset.sum_range_reflect
    (fun j => p.coeff j * seqAt x N (k + j)) (r + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  rw [hrefl]
  have hw : sh k (seqAt x N) ∈ W := hK k hk
  have h0 := congrArg (fun (w : W) => (w : ℕ → ℂ) 0)
    (show Polynomial.aeval T p ⟨_, hw⟩ = 0 by rw [hp, LinearMap.zero_apply])
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_zero, Pi.zero_apply, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, hTpow, sh_apply,
    smul_eq_mul, zero_add, ← hr] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [seqAt_apply]
  ring_nf

private theorem shiftFinite_add {s r : ℕ → ℂ}
    (hs : ShiftFinite s) (hr : ShiftFinite r) : ShiftFinite (s + r) := by
  obtain ⟨W₁, hfd₁, hW₁, K₁, hK₁⟩ := hs
  obtain ⟨W₂, hfd₂, hW₂, K₂, hK₂⟩ := hr
  have := hfd₁
  have := hfd₂
  refine ⟨W₁ ⊔ W₂, Submodule.finiteDimensional_sup W₁ W₂, ?_,
    max K₁ K₂, fun k hk => ?_⟩
  · intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := Submodule.mem_sup.mp hf
    rw [map_add]
    exact Submodule.add_mem_sup (hW₁ _ h₁) (hW₂ _ h₂)
  · rw [map_add]
    exact Submodule.add_mem_sup (hK₁ k (le_trans (le_max_left _ _) hk))
      (hK₂ k (le_trans (le_max_right _ _) hk))

private theorem sh_mul (k : ℕ) (f g : ℕ → ℂ) :
    sh k (f * g) = sh k f * sh k g := rfl

private theorem shiftFinite_mul {s r : ℕ → ℂ}
    (hs : ShiftFinite s) (hr : ShiftFinite r) : ShiftFinite (s * r) := by
  obtain ⟨W₁, hfd₁, hW₁, K₁, hK₁⟩ := hs
  obtain ⟨W₂, hfd₂, hW₂, K₂, hK₂⟩ := hr
  have := hfd₁
  have := hfd₂
  let μ : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) :=
    LinearMap.mul ℂ (ℕ → ℂ)
  have hμ : ∀ f g : ℕ → ℂ, μ f g = f * g := fun _ _ => rfl
  let W := Submodule.map₂ μ W₁ W₂
  have hfg : W.FG := Submodule.FG.map₂ μ
    (Module.Finite.iff_fg.mp inferInstance)
    (Module.Finite.iff_fg.mp inferInstance)
  refine ⟨W, Module.Finite.iff_fg.mpr hfg, ?_, max K₁ K₂, fun k hk => ?_⟩
  · intro f hf
    have hle : W ≤ W.comap (sh 1) := by
      refine Submodule.map₂_le.mpr fun f hf g hg => ?_
      rw [Submodule.mem_comap, hμ, sh_mul]
      exact Submodule.apply_mem_map₂ μ (hW₁ f hf) (hW₂ g hg)
    exact hle hf
  · rw [sh_mul, ← hμ]
    exact Submodule.apply_mem_map₂ μ (hK₁ k (le_trans (le_max_left _ _) hk))
      (hK₂ k (le_trans (le_max_right _ _) hk))

private def dil (e r : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f i := if e ∣ i + r then f ((i + r) / e) else 0
  map_add' f g := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

@[simp] private theorem dil_apply (e r : ℕ) (f : ℕ → ℂ) (i : ℕ) :
    dil e r f i = if e ∣ i + r then f ((i + r) / e) else 0 := rfl

private theorem sh_one_dil (e r : ℕ) (f : ℕ → ℂ) :
    sh 1 (dil e r f) = dil e (r + 1) f := by
  funext i
  simp only [sh_apply, dil_apply]
  rw [show i + 1 + r = i + (r + 1) by omega]

private theorem dil_add_mul (e r q : ℕ) (he : 0 < e) (f : ℕ → ℂ) :
    dil e (r + e * q) f = dil e r (sh q f) := by
  funext i
  simp only [dil_apply, sh_apply]
  rw [show i + (r + e * q) = i + r + e * q by omega]
  have hdvd : (e ∣ i + r + e * q) ↔ (e ∣ i + r) :=
    Nat.dvd_add_left (Dvd.intro q rfl)
  by_cases h : e ∣ i + r
  · rw [ite_eq_left (hdvd.mpr h), ite_eq_left h, Nat.add_mul_div_left _ _ he]
  · rw [ite_eq_right (fun h' => h (hdvd.mp h')), ite_eq_right h]

private theorem sh_dil_zero (e k : ℕ) (he : 0 < e) (f : ℕ → ℂ) :
    sh k (dil e 0 f) = dil e (k % e) (sh (k / e) f) := by
  have : sh k (dil e 0 f) = dil e k f := by
    funext i
    simp only [sh_apply, dil_apply, add_zero]
  rw [this]
  have h2 := dil_add_mul e (k % e) (k / e) he f
  rwa [Nat.mod_add_div] at h2

private theorem shiftFinite_dil {s : ℕ → ℂ} (hs : ShiftFinite s)
    (e : ℕ) (he : 0 < e) : ShiftFinite (dil e 0 s) := by
  classical
  obtain ⟨W, hfd, hW, K, hK⟩ := hs
  have := hfd
  let W' : Submodule ℂ (ℕ → ℂ) := ⨆ r : Fin e, W.map (dil e r)
  refine ⟨W', Submodule.finiteDimensional_iSup _, ?_, e * K, fun k hk => ?_⟩
  · intro f hf
    refine Submodule.iSup_induction _ (motive := fun f => sh 1 f ∈ W') hf ?_
      (by rw [map_zero]; exact W'.zero_mem)
      (fun a b ha hb => by rw [map_add]; exact W'.add_mem ha hb)
    rintro ⟨r, hr⟩ f hf
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
    rw [sh_one_dil]
    by_cases hre : r + 1 < e
    · exact Submodule.mem_iSup_of_mem ⟨r + 1, hre⟩ (Submodule.mem_map_of_mem hg)
    · have hr1 : r + 1 = 0 + e * 1 := by omega
      rw [hr1, dil_add_mul e 0 1 he]
      exact Submodule.mem_iSup_of_mem ⟨0, he⟩
        (Submodule.mem_map_of_mem (hW g hg))
  · rw [sh_dil_zero e k he]
    refine Submodule.mem_iSup_of_mem ⟨k % e, Nat.mod_lt _ he⟩
      (Submodule.mem_map_of_mem (hK _ ?_))
    exact (Nat.le_div_iff_mul_le he).mpr (by rw [mul_comm]; exact hk)

private def convR (v : ℕ → ℂ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f m := ∑ i ∈ Finset.range (m + 1), f i * v (m - i)
  map_add' f g := by
    funext m
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_assoc]

@[simp] private theorem convR_apply (v f : ℕ → ℂ) (m : ℕ) :
    convR v f m = ∑ i ∈ Finset.range (m + 1), f i * v (m - i) := rfl

private theorem sh_one_convR (v f : ℕ → ℂ) :
    sh 1 (convR v f) = f 0 • sh 1 v + convR v (sh 1 f) := by
  funext m
  simp only [sh_apply, convR_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_range_succ', add_comm]
  simp only [Nat.sub_zero, Nat.add_sub_add_right]

private theorem shiftFinite_convR {u v : ℕ → ℂ}
    (hu : ShiftFinite u) (hv : ShiftFinite v) : ShiftFinite (convR v u) := by
  classical
  obtain ⟨Wu, hfdu, hWu, Ku, hKu⟩ := hu
  obtain ⟨Wv, hfdv, hWv, Kv, hKv⟩ := hv
  have := hfdu
  have := hfdv
  let V : Submodule ℂ (ℕ → ℂ) :=
    Submodule.span ℂ ((fun l : Fin (Kv + 1) => sh l v) '' Set.univ) ⊔ Wv
  have hVsh : ∀ l, sh l v ∈ V := by
    intro l
    by_cases hl : l < Kv + 1
    · exact Submodule.mem_sup_left
        (Submodule.subset_span ⟨⟨l, hl⟩, Set.mem_univ _, rfl⟩)
    · exact Submodule.mem_sup_right (hKv l (by omega))
  have hVst : ∀ f ∈ V, sh 1 f ∈ V := by
    intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := Submodule.mem_sup.mp hf
    rw [map_add]
    refine V.add_mem ?_ (Submodule.mem_sup_right (hWv _ h₂))
    refine Submodule.span_induction (fun g hg => ?_)
      (by rw [map_zero]; exact V.zero_mem)
      (fun a b _ _ ha hb => by rw [map_add]; exact V.add_mem ha hb)
      (fun c a _ ha => by rw [map_smul]; exact V.smul_mem c ha) h₁
    obtain ⟨⟨l, _⟩, _, rfl⟩ := hg
    rw [sh_one_sh]
    exact hVsh _
  have hVfd : FiniteDimensional ℂ V := by
    have : FiniteDimensional ℂ
        (Submodule.span ℂ ((fun l : Fin (Kv + 1) => sh l v) '' Set.univ)) :=
      FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
    exact Submodule.finiteDimensional_sup _ _
  let W : Submodule ℂ (ℕ → ℂ) := Wu.map (convR v) ⊔ V
  have hdiff : ∀ k, sh k (convR v u) - convR v (sh k u) ∈ V := by
    intro k
    induction k with
    | zero => rw [sh_zero, sh_zero, sub_self]; exact V.zero_mem
    | succ k ih =>
      have e : sh (k + 1) (convR v u) - convR v (sh (k + 1) u) =
          sh 1 (sh k (convR v u) - convR v (sh k u)) +
            (sh k u) 0 • sh 1 v := by
        rw [map_sub, sh_one_sh, sh_one_convR, sh_one_sh]
        abel
      rw [e]
      exact V.add_mem (hVst _ ih) (V.smul_mem _ (hVsh 1))
  refine ⟨W, ?_, ?_, Ku, fun k hk => ?_⟩
  · have := hVfd
    exact Submodule.finiteDimensional_sup _ _
  · intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := Submodule.mem_sup.mp hf
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp h₁
    rw [map_add, sh_one_convR]
    exact W.add_mem
      (W.add_mem (Submodule.mem_sup_right (V.smul_mem _ (hVsh 1)))
        (Submodule.mem_sup_left (Submodule.mem_map_of_mem (hWu g hg))))
      (Submodule.mem_sup_right (hVst _ h₂))
  · rw [show sh k (convR v u) =
        (sh k (convR v u) - convR v (sh k u)) + convR v (sh k u) by abel]
    exact W.add_mem (Submodule.mem_sup_right (hdiff k))
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem (hKu k hk)))

private theorem shiftFinite_seqAt_any {x : ℤ → ℂ}
    (hx : SR x) (N : ℤ) : ShiftFinite (seqAt x N) := by
  obtain ⟨N₀, D, M, hD, _, hrec⟩ := hx
  have hs := shiftFinite_of_rec x N₀ D M hD hrec
  by_cases h : N ≤ N₀
  · refine shiftFinite_of_eventually hs (N₀ - N).toNat 0 0 fun k _ => ?_
    funext n
    simp only [sh_apply, seqAt_apply, add_zero, Nat.cast_add]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr h)]
    congr 1
    ring
  · refine shiftFinite_of_eventually hs 0 (N - N₀).toNat 0 fun k _ => ?_
    funext n
    simp only [sh_apply, seqAt_apply, add_zero, Nat.cast_add]
    rw [Int.toNat_of_nonneg (by omega)]
    congr 1
    ring

private theorem shiftFinite_zero : ShiftFinite (0 : ℕ → ℂ) :=
  ⟨⊥, inferInstance, fun f hf => by
    rw [(Submodule.mem_bot ℂ).mp hf, map_zero]
    exact Submodule.zero_mem _, 0, fun k _ => by
      rw [map_zero]
      exact Submodule.zero_mem _⟩

private theorem shiftFinite_sum {ι : Type} (s : Finset ι)
    (f : ι → ℕ → ℂ) (h : ∀ i ∈ s, ShiftFinite (f i)) :
    ShiftFinite (fun m => ∑ i ∈ s, f i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact shiftFinite_zero
  | insert a s ha ih =>
    have : (fun m => ∑ i ∈ insert a s, f i m) =
        f a + fun m => ∑ i ∈ s, f i m := by
      funext m
      rw [Finset.sum_insert ha]
      rfl
    rw [this]
    exact shiftFinite_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem shiftFinite_geom (c α : ℂ) :
    ShiftFinite (fun m => c * α ^ m) := by
  let g : ℕ → ℂ := fun m => c * α ^ m
  refine ⟨Submodule.span ℂ {g},
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _), ?_,
    0, fun k _ => ?_⟩
  · intro f hf
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
    rw [map_smul]
    refine Submodule.smul_mem _ _
      (Submodule.mem_span_singleton.mpr ⟨α, ?_⟩)
    funext n
    simp only [sh_apply, Pi.smul_apply, smul_eq_mul, g, pow_succ]
    ring
  · refine Submodule.mem_span_singleton.mpr ⟨α ^ k, ?_⟩
    funext n
    simp only [sh_apply, Pi.smul_apply, smul_eq_mul, g, pow_add]
    ring

private theorem exists_coord (E : LinearRecurrence ℂ) :
    ∃ σ : Fin E.order → ℕ → ℂ, (∀ k, E.IsSolution (σ k)) ∧
      ∀ s, E.IsSolution s → s = fun m => ∑ k : Fin E.order, s k * σ k m := by
  classical
  refine ⟨fun k => E.basis k, fun k => (E.basis k).property, fun s hs => ?_⟩
  have h := E.basis.sum_repr ⟨s, hs⟩
  funext m
  have hm := congrArg (fun w : E.solSpace => (w : ℕ → ℂ) m) h
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, LinearRecurrence.repr_basis_apply] using hm.symm

private def boxLine (e₁ e₂ : ℕ) (w : ℕ → ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
    if e₁ * j + e₂ * l = m then w j l else 0

private theorem finsum_line_eq_boxLine (w : ℤ × ℤ → ℂ) (N₁ N₂ : ℤ)
    (hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₂) → w n = 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂) (m : ℕ) :
    (∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 =
      ((e₁ : ℤ) * N₁ + (e₂ : ℤ) * N₂) + (m : ℤ) then w n else 0) =
      boxLine e₁ e₂ (fun j l => w (N₁ + j, N₂ + l)) m := by
  classical
  set N : ℤ := (e₁ : ℤ) * N₁ + (e₂ : ℤ) * N₂ with hN
  let F : ℤ × ℤ → ℂ := fun n =>
    if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = N + (m : ℤ) then w n else 0
  let B : Finset (ℤ × ℤ) :=
    Finset.Icc N₁ (N₁ + m) ×ˢ Finset.Icc N₂ (N₂ + m)
  have hsupp : F.support ⊆ (B : Set (ℤ × ℤ)) := by
    intro n hn
    simp only [Function.mem_support, F, ne_eq, ite_eq_right_iff,
      not_forall, exists_prop] at hn
    obtain ⟨hl, hne⟩ := hn
    have hx1 : N₁ ≤ n.1 := by
      by_contra h
      exact hne (hw _ (Or.inl (not_le.mp h)))
    have hy1 : N₂ ≤ n.2 := by
      by_contra h
      exact hne (hw _ (Or.inr (not_le.mp h)))
    have he₁' : (1 : ℤ) ≤ e₁ := by exact_mod_cast he₁
    have he₂' : (1 : ℤ) ≤ e₂ := by exact_mod_cast he₂
    simp only [B, Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨hx1, ?_⟩, ⟨hy1, ?_⟩⟩ <;> nlinarith
  rw [finsum_eq_sum_of_support_subset F hsupp]
  have hB : B = (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).image
      (fun p : ℕ × ℕ => ((N₁ + p.1 : ℤ), (N₂ + p.2 : ℤ))) := by
    ext n
    simp only [B, Finset.mem_product, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range, Prod.ext_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      refine ⟨((n.1 - N₁).toNat, (n.2 - N₂).toNat),
        ⟨by omega, by omega⟩, ?_, ?_⟩
      · simp only
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      · simp only
        rw [Int.toNat_of_nonneg (by omega)]
        ring
    · rintro ⟨p, ⟨h1, h2⟩, h3, h4⟩
      rw [← h3, ← h4]
      omega
  rw [hB, Finset.sum_image (fun p _ q _ h => by
    simp only [Prod.ext_iff] at h
    exact Prod.ext (by exact_mod_cast (add_left_cancel h.1))
      (by exact_mod_cast (add_left_cancel h.2)))]
  rw [boxLine, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [F]
  have hline : ((e₁ : ℤ) * (N₁ + (p.1 : ℤ)) +
      (e₂ : ℤ) * (N₂ + (p.2 : ℤ)) = N + (m : ℤ)) ↔
      (e₁ * p.1 + e₂ * p.2 = m) := by
    rw [hN]
    constructor
    · intro h
      have : ((e₁ * p.1 + e₂ * p.2 : ℕ) : ℤ) = m := by
        push_cast
        linear_combination h
      exact_mod_cast this
    · intro h
      have : ((e₁ * p.1 + e₂ * p.2 : ℕ) : ℤ) = m := by exact_mod_cast h
      push_cast at this
      linear_combination this
  simp only [hline]

private theorem boxLine_sum {ι : Type} (e₁ e₂ : ℕ) (s : Finset ι)
    (w : ι → ℕ → ℕ → ℂ) (m : ℕ) :
    boxLine e₁ e₂ (fun j l => ∑ k ∈ s, w k j l) m =
      ∑ k ∈ s, boxLine e₁ e₂ (w k) m := by
  simp only [boxLine]
  have e1 : (∑ j ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
      if e₁ * j + e₂ * l = m then ∑ k ∈ s, w k j l else 0) =
      ∑ j ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
        ∑ k ∈ s, if e₁ * j + e₂ * l = m then w k j l else 0 := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [e1]
  have e2 : ∀ j ∈ Finset.range (m + 1),
      (∑ l ∈ Finset.range (m + 1), ∑ k ∈ s,
        if e₁ * j + e₂ * l = m then w k j l else 0) =
      ∑ k ∈ s, ∑ l ∈ Finset.range (m + 1),
        if e₁ * j + e₂ * l = m then w k j l else 0 :=
    fun j _ => Finset.sum_comm
  rw [Finset.sum_congr rfl e2, Finset.sum_comm]

private theorem boxLine_mul (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (p q : ℕ → ℂ) (m : ℕ) :
    boxLine e₁ e₂ (fun j l => p j * q l) m =
      convR (dil e₂ 0 q) (dil e₁ 0 p) m := by
  classical
  rw [boxLine, ← Finset.sum_product', convR_apply]
  have hrhs : ∀ i ∈ Finset.range (m + 1),
      dil e₁ 0 p i * dil e₂ 0 q (m - i) =
      if e₁ ∣ i ∧ e₂ ∣ (m - i) then p (i / e₁) * q ((m - i) / e₂) else 0 := by
    intro i _
    simp only [dil_apply, add_zero]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl hrhs, ← Finset.sum_filter,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  symm
  refine Finset.sum_nbij' (fun i => (i / e₁, (m - i) / e₂))
    (fun jl => e₁ * jl.1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨him, ⟨a, ha⟩, ⟨c, hc⟩⟩ := hi
    have ha' : i / e₁ = a := by rw [ha, Nat.mul_div_cancel_left _ he₁]
    have hc' : (m - i) / e₂ = c := by rw [hc, Nat.mul_div_cancel_left _ he₂]
    have hale : a ≤ i := by rw [ha]; exact Nat.le_mul_of_pos_left a he₁
    have hcle : c ≤ m - i := by rw [hc]; exact Nat.le_mul_of_pos_left c he₂
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      ha', hc']
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  · intro jl hjl
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hjl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hjl
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ⟨jl.1, rfl⟩, ?_⟩
    rw [show m - e₁ * jl.1 = e₂ * jl.2 by omega]
    exact ⟨jl.2, rfl⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨_, ⟨a, ha⟩, _⟩ := hi
    simp only
    rw [ha, Nat.mul_div_cancel_left _ he₁]
  · intro jl hjl
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hjl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hjl
    refine Prod.ext ?_ ?_
    · exact Nat.mul_div_cancel_left _ he₁
    · change (m - e₁ * jl.1) / e₂ = jl.2
      rw [show m - e₁ * jl.1 = e₂ * jl.2 by omega]
      exact Nat.mul_div_cancel_left _ he₂
  · intro i _; rfl

private theorem eq_zero_of_rec_all (g : ℤ → ℂ) (N : ℤ)
    (hN : ∀ m : ℤ, m < N → g m = 0) (D : Polynomial ℂ)
    (hD : D.eval 0 ≠ 0)
    (hrec : ∀ m : ℕ, ∑ i ∈ Finset.range (D.natDegree + 1),
      D.coeff i * g (N + (m : ℤ) - (i : ℤ)) = 0) :
    ∀ m : ℤ, g m = 0 := by
  have hD0 : D.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  have key : ∀ m : ℕ, g (N + m) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      have h := hrec m
      rw [Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)] at h
      have hrest : ∑ i ∈ Finset.Ico 1 (D.natDegree + 1),
          D.coeff i * g (N + (m : ℤ) - (i : ℤ)) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        by_cases him : i ≤ m
        · have hz := ih (m - i) (by omega)
          rw [show N + (m : ℤ) - (i : ℤ) =
              N + ((m - i : ℕ) : ℤ) by omega, hz, mul_zero]
        · rw [hN _ (by omega), mul_zero]
      rw [hrest, add_zero, Nat.cast_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hD0
  intro m
  by_cases hm : m < N
  · exact hN m hm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = N + k :=
      ⟨(m - N).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    exact key k

private theorem row_rec (A : ℤ × ℤ → ℂ) (N₁ : ℤ)
    (D₁ D₂ : Polynomial ℂ) (M : ℕ) (hD₁ : D₁.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
      ∑ i ∈ Finset.range (D₁.natDegree + 1),
        ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l *
            A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)
    (z : ℤ) (m₂ : ℕ) (hm₂ : M ≤ m₂) :
    ∑ l ∈ Finset.range (D₂.natDegree + 1),
      D₂.coeff l * A (z, N₁ + (m₂ : ℤ) - (l : ℤ)) = 0 := by
  let g : ℤ → ℂ := fun z => ∑ l ∈ Finset.range (D₂.natDegree + 1),
    D₂.coeff l * A (z, N₁ + (m₂ : ℤ) - (l : ℤ))
  have hg : ∀ m : ℤ, g m = 0 := by
    refine eq_zero_of_rec_all g N₁ (fun m hm => ?_) D₁ hD₁ (fun m₁ => ?_)
    · exact Finset.sum_eq_zero fun l _ => by
        rw [hsupp _ (Or.inl hm), mul_zero]
    · have h := hrec m₁ m₂ (Or.inr hm₂)
      simp only [g, Finset.mul_sum, ← mul_assoc]
      exact h
  exact hg z

private theorem col_rec (A : ℤ × ℤ → ℂ) (N₁ : ℤ)
    (D₁ D₂ : Polynomial ℂ) (M : ℕ) (hD₂ : D₂.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
      ∑ i ∈ Finset.range (D₁.natDegree + 1),
        ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l *
            A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)
    (z : ℤ) (m₁ : ℕ) (hm₁ : M ≤ m₁) :
    ∑ i ∈ Finset.range (D₁.natDegree + 1),
      D₁.coeff i * A (N₁ + (m₁ : ℤ) - (i : ℤ), z) = 0 := by
  let g : ℤ → ℂ := fun z => ∑ i ∈ Finset.range (D₁.natDegree + 1),
    D₁.coeff i * A (N₁ + (m₁ : ℤ) - (i : ℤ), z)
  have hg : ∀ m : ℤ, g m = 0 := by
    refine eq_zero_of_rec_all g N₁ (fun m hm => ?_) D₂ hD₂ (fun m₂ => ?_)
    · exact Finset.sum_eq_zero fun i _ => by
        rw [hsupp _ (Or.inr hm), mul_zero]
    · have h := hrec m₁ m₂ (Or.inl hm₁)
      simp only [g, Finset.mul_sum]
      rw [Finset.sum_comm, ← h]
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun l _ => by ring
  exact hg z

/-- Positive weighted line sums preserve lower-supported eventual backward
recurrences. The separated recurrence holds when either coordinate is large;
the two input support witnesses are independent. No coprimality is required.

Adapted from the frozen FLT weighted-line closure, entry229 (line source only).
The finite separated expansion uses the canonical recurrence solution basis. -/
public theorem exists_recurrence_weighted_line
    (A : ℤ × ℤ → ℂ) (b : ℤ → ℂ) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ),
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1),
          ∑ l ∈ Finset.range (D₂.natDegree + 1),
            D₁.coeff i * D₂.coeff l *
              A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))
    (hb : ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → b m = 0) ∧
      (∀ m : ℕ, M' ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * b (N₂ + (m : ℤ) - (i : ℤ)) = 0)) :
    ∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then
          A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
          if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then
            A n * b n.1 * α ^ n.1 * β ^ n.2 else 0)
          (N + (m : ℤ) - (i : ℤ)) = 0) := by
  classical
  obtain ⟨N₁, D₁, D₂, M, hD₁, hD₂, hsupp, hrec⟩ := hA
  have hbSR : SR b := hb
  let w : ℤ × ℤ → ℂ := fun n => A n * b n.1 * α ^ n.1 * β ^ n.2
  have hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → w n = 0 := by
    intro n hn
    simp only [w, hsupp n hn, zero_mul]
  set N : ℤ := (e₁ : ℤ) * N₁ + (e₂ : ℤ) * N₁ with hN
  set K := max M D₂.natDegree with hK
  let E := backwardRecurrence D₂ K
  obtain ⟨σ, hσ, hcoord⟩ := exists_coord E
  have hrow : ∀ j : ℕ, E.IsSolution (fun l : ℕ => A (N₁ + j, N₁ + l)) := by
    intro j
    apply (isSolution_iff_backward D₂ hD₂ K (le_max_right _ _) _).mpr
    intro m hm
    have h := row_rec A N₁ D₁ D₂ M hD₁ hsupp hrec (N₁ + j) m
      (le_trans (le_max_left _ _) hm)
    rw [← h]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ m := le_trans
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
      (le_trans (le_max_right _ _) hm)
    congr 2
    push_cast [Nat.cast_sub hl']
    ring
  have hdec : ∀ j l : ℕ, A (N₁ + j, N₁ + l) =
      ∑ k : Fin K, A (N₁ + j, N₁ + ((k : ℕ) : ℤ)) * σ k l := by
    intro j l
    exact congrFun (hcoord _ (hrow j)) l
  have hcolSF : ∀ k : ℕ,
      ShiftFinite (fun j : ℕ => A (N₁ + (j : ℤ), N₁ + (k : ℤ))) := fun k =>
    shiftFinite_of_rec (fun z => A (z, N₁ + k)) N₁ D₁ M hD₁
      (fun m hm => col_rec A N₁ D₁ D₂ M hD₂ hsupp hrec (N₁ + k) m hm)
  have hσSF : ∀ k, ShiftFinite (σ k) :=
    fun k => shiftFinite_of_isSolution E _ (hσ k)
  have hbSF : ShiftFinite (seqAt b N₁) := shiftFinite_seqAt_any hbSR N₁
  have hαSF : ShiftFinite (fun j : ℕ => α ^ (N₁ + (j : ℤ))) := by
    have : (fun j : ℕ => α ^ (N₁ + (j : ℤ))) =
        fun j => α ^ N₁ * α ^ j := by
      funext j
      rw [zpow_add₀ hα, zpow_natCast]
    rw [this]
    exact shiftFinite_geom _ _
  have hβSF : ShiftFinite (fun l : ℕ => β ^ (N₁ + (l : ℤ))) := by
    have : (fun l : ℕ => β ^ (N₁ + (l : ℤ))) =
        fun l => β ^ N₁ * β ^ l := by
      funext l
      rw [zpow_add₀ hβ, zpow_natCast]
    rw [this]
    exact shiftFinite_geom _ _
  let p : Fin K → ℕ → ℂ := fun k j =>
    A (N₁ + (j : ℤ), N₁ + ((k : ℕ) : ℤ)) * b (N₁ + j) * α ^ (N₁ + (j : ℤ))
  let q : Fin K → ℕ → ℂ := fun k l => σ k l * β ^ (N₁ + (l : ℤ))
  have hpSF : ∀ k, ShiftFinite (p k) := fun k =>
    shiftFinite_mul (shiftFinite_mul (hcolSF k) hbSF) hαSF
  have hqSF : ∀ k, ShiftFinite (q k) :=
    fun k => shiftFinite_mul (hσSF k) hβSF
  have hline : seqAt (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
      if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then
        A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) N =
      fun m => ∑ k : Fin K, convR (dil e₂ 0 (q k)) (dil e₁ 0 (p k)) m := by
    funext m
    rw [seqAt_apply]
    have h1 := finsum_line_eq_boxLine w N₁ N₁ hw e₁ e₂ he₁ he₂ m
    simp only [w] at h1
    rw [h1]
    have h2 : (fun j l : ℕ =>
        A (N₁ + (j : ℤ), N₁ + (l : ℤ)) * b (N₁ + (j : ℤ)) *
          α ^ (N₁ + (j : ℤ)) * β ^ (N₁ + (l : ℤ))) =
        fun j l => ∑ k : Fin K, p k j * q k l := by
      funext j l
      simp only [p, q, hdec j l, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h2, boxLine_sum]
    exact Finset.sum_congr rfl fun k _ =>
      boxLine_mul e₁ e₂ he₁ he₂ (p k) (q k) m
  refine sr_of_shiftFinite _ N (fun t ht => ?_) ?_
  · have : (fun n : ℤ × ℤ =>
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then
          A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) = fun _ => 0 := by
      funext n
      split_ifs with h
      · by_cases h1 : n.1 < N₁
        · rw [hsupp _ (Or.inl h1), zero_mul, zero_mul, zero_mul]
        · by_cases h2 : n.2 < N₁
          · rw [hsupp _ (Or.inr h2), zero_mul, zero_mul, zero_mul]
          · exfalso
            have he₁' : (0 : ℤ) ≤ e₁ := by exact_mod_cast he₁.le
            have he₂' : (0 : ℤ) ≤ e₂ := by exact_mod_cast he₂.le
            have : N ≤ t := by rw [← h, hN]; nlinarith
            exact absurd ht (not_lt.mpr this)
      · rfl
    simp only [this, finsum_zero]
  · rw [hline]
    exact shiftFinite_sum _ _ fun k _ => shiftFinite_convR
      (shiftFinite_dil (hpSF k) e₁ he₁) (shiftFinite_dil (hqSF k) e₂ he₂)

end Polynomial
