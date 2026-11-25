/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

private theorem collinear_of_forall_triple_collinear (S : Set (EuclideanSpace ℝ (Fin 2)))
    (h : ∀ A ∈ S, ∀ B ∈ S, ∀ C ∈ S,
      Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) :
    Collinear ℝ S := by
  by_cases hempty : S = ∅
  · subst hempty; exact collinear_empty ℝ _
  · obtain ⟨A, hA⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    by_cases hsingle : ∀ B ∈ S, B = A
    · refine Collinear.subset ?_ (collinear_singleton ℝ A)
      intro P hP
      simp only [Set.mem_singleton_iff]
      exact hsingle P hP
    · push Not at hsingle
      obtain ⟨B, hB, hne⟩ := hsingle
      rw [collinear_iff_of_mem hA]
      refine ⟨B -ᵥ A, fun P hP => ?_⟩
      obtain ⟨p₀, v, hrep⟩ :=
        (collinear_iff_exists_forall_eq_smul_vadd _).mp (h A hA B hB P hP)
      obtain ⟨rA, hrA⟩ := hrep A (by simp)
      obtain ⟨rB, hrB⟩ := hrep B (by simp)
      obtain ⟨rP, hrP⟩ := hrep P (by simp)
      have key : ∀ r₁ r₂ : ℝ, ∀ q₁ q₂ : EuclideanSpace ℝ (Fin 2),
          q₁ = r₁ • v +ᵥ p₀ → q₂ = r₂ • v +ᵥ p₀ → q₁ -ᵥ q₂ = (r₁ - r₂) • v := by
        intro r₁ r₂ q₁ q₂ h1 h2
        rw [h1, h2, vsub_eq_sub, vadd_eq_add, vadd_eq_add, sub_smul]
        abel
      have hBA : B -ᵥ A = (rB - rA) • v := key rB rA B A hrB hrA
      have hPA : P -ᵥ A = (rP - rA) • v := key rP rA P A hrP hrA
      have hrr : rB - rA ≠ 0 := by
        intro hcon
        apply hne
        have hzero : B -ᵥ A = 0 := by rw [hBA, hcon, zero_smul]
        exact vsub_eq_zero_iff_eq.mp hzero
      have hv : v = (rB - rA)⁻¹ • (B -ᵥ A) := by
        rw [hBA, ← mul_smul, inv_mul_cancel₀ hrr, one_smul]
      refine ⟨(rP - rA) * (rB - rA)⁻¹, ?_⟩
      have hPv : P -ᵥ A = ((rP - rA) * (rB - rA)⁻¹) • (B -ᵥ A) := by
        rw [hPA, hv, ← mul_smul]
      calc P = (P -ᵥ A) +ᵥ A := (vsub_vadd P A).symm
        _ = ((rP - rA) * (rB - rA)⁻¹) • (B -ᵥ A) +ᵥ A := by rw [hPv]

private theorem fiber_finite (A B C : EuclideanSpace ℝ (Fin 2))
    (haff : AffineIndependent ℝ ![A, B, C]) (k' v' : ℝ) :
    Set.Finite {P : EuclideanSpace ℝ (Fin 2) |
      dist P A - dist P B = k' ∧ dist P A - dist P C = v'} := by
  have hfam : LinearIndependent ℝ
      (fun i : {x : Fin 3 // x ≠ 0} => ![A, B, C] (↑i) -ᵥ ![A, B, C] 0) :=
    (affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] 0).mp haff
  let e : Fin 2 → {x : Fin 3 // x ≠ 0} := ![⟨1, by decide⟩, ⟨2, by decide⟩]
  have he : Function.Injective e := by decide
  have hcomp := hfam.comp e he
  have hli : LinearIndependent ℝ ![B -ᵥ A, C -ᵥ A] := by
    have heq : (fun i : {x : Fin 3 // x ≠ 0} => ![A, B, C] (↑i) -ᵥ ![A, B, C] 0) ∘ e
        = ![B -ᵥ A, C -ᵥ A] := by
      rw [funext_iff, Fin.forall_fin_two]
      refine ⟨?_, ?_⟩
      · change ![A, B, C] 1 -ᵥ ![A, B, C] 0 = B -ᵥ A
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      · change ![A, B, C] 2 -ᵥ ![A, B, C] 0 = C -ᵥ A
        simp [Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
    rwa [heq] at hcomp
  have hspan : Submodule.span ℝ (Set.range ![B -ᵥ A, C -ᵥ A]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  let φ : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun p => ![inner ℝ p (B -ᵥ A), inner ℝ p (C -ᵥ A)],
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [inner_add_left, Matrix.cons_val_zero,
          Matrix.cons_val_one, Pi.add_apply]
      map_smul' := by
        intro r x
        funext i
        fin_cases i <;> simp [real_inner_smul_left, Matrix.cons_val_zero,
          Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul] }
  have hφapp : ∀ p : EuclideanSpace ℝ (Fin 2), ∀ i : Fin 2,
      φ p i = ![inner ℝ p (B -ᵥ A), inner ℝ p (C -ᵥ A)] i := fun p i => rfl
  have hker : ∀ x : EuclideanSpace ℝ (Fin 2), φ x = 0 → x = 0 := by
    intro x hx
    have hb0 : inner ℝ x (B -ᵥ A) = 0 := by
      have h0 := hφapp x 0
      rw [hx] at h0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
      exact h0.symm
    have hc0 : inner ℝ x (C -ᵥ A) = 0 := by
      have h1 := hφapp x 1
      rw [hx] at h1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h1
      exact h1.symm
    have hmem : x ∈ Submodule.span ℝ (Set.range ![B -ᵥ A, C -ᵥ A]) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    have hself : inner ℝ x x = 0 := by
      have hrewrite : inner ℝ x x
          = inner ℝ x (∑ i, cf i • ![B -ᵥ A, C -ᵥ A] i) := by rw [hcf]
      have e0 : inner ℝ x (cf 0 • ![B -ᵥ A, C -ᵥ A] 0) = 0 := by
        rw [Matrix.cons_val_zero, real_inner_smul_right, hb0, mul_zero]
      have e1 : inner ℝ x (cf 1 • ![B -ᵥ A, C -ᵥ A] 1) = 0 := by
        rw [Matrix.cons_val_one, Matrix.cons_val_zero, real_inner_smul_right,
          hc0, mul_zero]
      rw [hrewrite, inner_sum, Fin.sum_univ_two, e0, e1, add_zero]
    exact inner_self_eq_zero.mp hself
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzero := hker _ h
    rwa [sub_eq_zero] at hzero
  have hrange : φ.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_of_inj hφinj
    rw [finrank_euclideanSpace_fin] at h1
    have h2 : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by
      rw [Module.finrank_pi, Fintype.card_fin]
    omega
  have hsurj : Function.Surjective φ := LinearMap.range_eq_top.mp hrange
  obtain ⟨u1, hu1⟩ := hsurj ![k', v']
  obtain ⟨u0, hu0⟩ := hsurj
    ![ (‖B -ᵥ A‖^2 - k'^2)/2, (‖C -ᵥ A‖^2 - v'^2)/2 ]
  have hkb : inner ℝ u1 (B -ᵥ A) = k' := by
    have h := hφapp u1 0
    rw [hu1] at h
    simp only [Matrix.cons_val_zero] at h
    exact h.symm
  have hI1 : ∀ P : EuclideanSpace ℝ (Fin 2),
      dist P A - dist P B = k' →
      inner ℝ (P -ᵥ A) (B -ᵥ A) =
        dist P A * k' + (‖B -ᵥ A‖^2 - k'^2)/2 := by
    intro P hdiff
    have hs : dist P B = dist P A - k' := by linarith [hdiff]
    have hPB : (P -ᵥ A) - (B -ᵥ A) = P - B := by
      rw [vsub_eq_sub, vsub_eq_sub]
      abel
    have hnorm : ‖(P -ᵥ A) - (B -ᵥ A)‖ = dist P B := by
      rw [hPB, dist_eq_norm]
    have hexpand := norm_sub_sq_real (P -ᵥ A) (B -ᵥ A)
    rw [hnorm] at hexpand
    have hPA : ‖P -ᵥ A‖ = dist P A := by
      rw [vsub_eq_sub, dist_eq_norm]
    rw [hPA] at hexpand
    have e1 : 2 * inner ℝ (P -ᵥ A) (B -ᵥ A)
        = (dist P A)^2 - (dist P B)^2 + ‖B -ᵥ A‖^2 := by
      linarith [hexpand]
    have e2 : (dist P A)^2 - (dist P B)^2 = (2 * dist P A - k') * k' := by
      rw [sq_sub_sq, hs]
      ring
    have e3 : (2 * dist P A - k') * k' = 2 * (dist P A * k') - k'^2 := by ring
    linarith [e1, e2, e3]
  have hI2 : ∀ P : EuclideanSpace ℝ (Fin 2),
      dist P A - dist P C = v' →
      inner ℝ (P -ᵥ A) (C -ᵥ A) =
        dist P A * v' + (‖C -ᵥ A‖^2 - v'^2)/2 := by
    intro P hdiff
    have hs : dist P C = dist P A - v' := by linarith [hdiff]
    have hPC : (P -ᵥ A) - (C -ᵥ A) = P - C := by
      rw [vsub_eq_sub, vsub_eq_sub]
      abel
    have hnorm : ‖(P -ᵥ A) - (C -ᵥ A)‖ = dist P C := by
      rw [hPC, dist_eq_norm]
    have hexpand := norm_sub_sq_real (P -ᵥ A) (C -ᵥ A)
    rw [hnorm] at hexpand
    have hPA : ‖P -ᵥ A‖ = dist P A := by
      rw [vsub_eq_sub, dist_eq_norm]
    rw [hPA] at hexpand
    have e1 : 2 * inner ℝ (P -ᵥ A) (C -ᵥ A)
        = (dist P A)^2 - (dist P C)^2 + ‖C -ᵥ A‖^2 := by
      linarith [hexpand]
    have e2 : (dist P A)^2 - (dist P C)^2 = (2 * dist P A - v') * v' := by
      rw [sq_sub_sq, hs]
      ring
    have e3 : (2 * dist P A - v') * v' = 2 * (dist P A * v') - v'^2 := by ring
    linarith [e1, e2, e3]
  have hφeq : ∀ P : EuclideanSpace ℝ (Fin 2),
      dist P A - dist P B = k' → dist P A - dist P C = v' →
      φ (P -ᵥ A) = (dist P A) • ![k', v'] +
        ![ (‖B -ᵥ A‖^2 - k'^2)/2, (‖C -ᵥ A‖^2 - v'^2)/2 ] := by
    intro P h1 h2
    have e1 := hI1 P h1
    have e2 := hI2 P h2
    funext i
    fin_cases i
    · rw [hφapp]
      simp only [Fin.mk_zero, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [e1]
    · rw [hφapp]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [e2]
  have hdet : ∀ P : EuclideanSpace ℝ (Fin 2),
      dist P A - dist P B = k' → dist P A - dist P C = v' →
      P -ᵥ A = (dist P A) • u1 + u0 := by
    intro P h1 h2
    apply hφinj
    rw [hφeq P h1 h2, map_add, map_smul, hu1, hu0]
  set q : Polynomial ℝ :=
    Polynomial.C (‖u1‖^2 - 1) * Polynomial.X^2 +
    Polynomial.C (2 * inner ℝ u1 u0) * Polynomial.X +
    Polynomial.C (‖u0‖^2) with hqdef
  have hroot : ∀ P : EuclideanSpace ℝ (Fin 2),
      dist P A - dist P B = k' → dist P A - dist P C = v' →
      q.IsRoot (dist P A) := by
    intro P h1 h2
    rw [Polynomial.IsRoot.def]
    have hdetP := hdet P h1 h2
    have hnorm : dist P A = ‖(dist P A) • u1 + u0‖ := by
      rw [← hdetP, vsub_eq_sub, ← dist_eq_norm]
    have e : (dist P A)^2 = ‖(dist P A) • u1 + u0‖^2 := congrArg (· ^ 2) hnorm
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg dist_nonneg, real_inner_smul_left] at e
    have hsq : (dist P A)^2 = (dist P A)^2 * ‖u1‖^2 +
        2 * (dist P A) * inner ℝ u1 u0 + ‖u0‖^2 := by
      linear_combination e
    rw [hqdef]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    linear_combination -hsq
  by_cases hq0 : q = 0
  · have hfalse : False := by
      have e0 : q.eval 0 = 0 := by rw [hq0]; exact Polynomial.eval_zero
      have e1 : q.eval 1 = 0 := by rw [hq0]; exact Polynomial.eval_zero
      have em1 : q.eval (-1) = 0 := by rw [hq0]; exact Polynomial.eval_zero
      rw [hqdef] at e0 e1 em1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at e0 e1 em1
      have hZ : ‖u0‖^2 = 0 := by linarith [e0]
      have ha : ‖u1‖^2 - 1 = 0 := by linarith [e1, em1, hZ]
      have hu0zero : u0 = 0 := by
        have h1 : ‖u0‖ = 0 := by
          have hnn := norm_nonneg u0
          nlinarith [hZ]
        exact norm_eq_zero.mp h1
      have hu1norm : ‖u1‖ = 1 := by
        have h2 : ‖u1‖^2 = 1 := by linarith [ha]
        rw [sq_eq_one_iff] at h2
        rcases h2 with h | h
        · exact h
        · exfalso
          have hnn := norm_nonneg u1
          linarith
      have hBb2 : ‖B -ᵥ A‖^2 = k'^2 := by
        have hw : (‖B -ᵥ A‖^2 - k'^2)/2 = 0 := by
          have h := congrFun hu0 0
          rw [hu0zero, map_zero] at h
          simp only [Matrix.cons_val_zero] at h
          have h0 : ((0 : Fin 2 → ℝ)) 0 = 0 := rfl
          rw [h0] at h
          exact h.symm
        linarith [hw]
      have hCc2 : ‖C -ᵥ A‖^2 = v'^2 := by
        have hw : (‖C -ᵥ A‖^2 - v'^2)/2 = 0 := by
          have h := congrFun hu0 1
          rw [hu0zero, map_zero] at h
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
          have h0 : ((0 : Fin 2 → ℝ)) 1 = 0 := rfl
          rw [h0] at h
          exact h.symm
        linarith [hw]
      have hcomm : inner ℝ (B -ᵥ A) u1 = k' := by
        rw [real_inner_comm]
        exact hkb
      have hu1sq : ‖u1‖^2 = 1 := by rw [hu1norm, one_pow]
      have hbeq : B -ᵥ A = k' • u1 := by
        have hnsmul : ‖k' • u1‖^2 = k'^2 := by
          rw [norm_smul, hu1norm, mul_one, Real.norm_eq_abs, sq_abs]
        have hexpand : inner ℝ (B -ᵥ A - k' • u1) (B -ᵥ A - k' • u1) = 0 := by
          simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
            real_inner_smul_right, real_inner_self_eq_norm_sq,
            hcomm, hkb, hBb2, hnsmul]
          ring
        have hzero : B -ᵥ A - k' • u1 = 0 := inner_self_eq_zero.mp hexpand
        rwa [sub_eq_zero] at hzero
      have hkcv : inner ℝ u1 (C -ᵥ A) = v' := by
        have h := hφapp u1 1
        rw [hu1] at h
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
        exact h.symm
      have hcommC : inner ℝ (C -ᵥ A) u1 = v' := by
        rw [real_inner_comm]
        exact hkcv
      have hceq : C -ᵥ A = v' • u1 := by
        have hnsmul : ‖v' • u1‖^2 = v'^2 := by
          rw [norm_smul, hu1norm, mul_one, Real.norm_eq_abs, sq_abs]
        have hexpand : inner ℝ (C -ᵥ A - v' • u1) (C -ᵥ A - v' • u1) = 0 := by
          simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
            real_inner_smul_right, real_inner_self_eq_norm_sq,
            hcommC, hkcv, hCc2, hnsmul]
          ring
        have hzero : C -ᵥ A - v' • u1 = 0 := inner_self_eq_zero.mp hexpand
        rwa [sub_eq_zero] at hzero
      have hcol : Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
        rw [collinear_iff_of_mem (by simp : A ∈ ({A, B, C} : Set _))]
        refine ⟨u1, fun P hP => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
        rcases hP with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨k', by rw [← hbeq, vsub_vadd]⟩
        · exact ⟨v', by rw [← hceq, vsub_vadd]⟩
      exact (collinear_iff_not_affineIndependent_set.mp hcol) haff
    exact False.elim hfalse
  · have hroots : {x : ℝ | q.IsRoot x}.Finite :=
      Polynomial.finite_setOfPred_isRoot hq0
    refine Set.Finite.of_injOn (f := fun P => dist P A)
      (t := {x : ℝ | q.IsRoot x}) ?_ ?_ hroots
    · intro P hP
      exact hroot P hP.1 hP.2
    · intro P1 hP1 P2 hP2 heq
      have heq' : dist P1 A = dist P2 A := heq
      have d1 := hdet P1 hP1.1 hP1.2
      have d2 := hdet P2 hP2.1 hP2.2
      rw [heq'] at d1
      calc P1 = (P1 -ᵥ A) +ᵥ A := (vsub_vadd P1 A).symm
        _ = (P2 -ᵥ A) +ᵥ A := by rw [d1, d2]
        _ = P2 := vsub_vadd P2 A

/-- **Erdős–Anning theorem.** An infinite set of points in the plane with pairwise
integer distances is collinear.

Proves `Wanted` entry `erdos_anning`.

Sources: N. H. Anning and P. Erdős, "Integral distances," Bull. Amer. Math. Soc. 51 (1945),
598–600; P. Erdős, "Integral distances," Bull. Amer. Math. Soc. 51 (1945), 996.
Overview: https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Anning_theorem
-/
theorem erdos_anning :
    ∀ (S : Set (EuclideanSpace ℝ (Fin 2))), S.Infinite →
      (∀ p ∈ S, ∀ q ∈ S, ∃ n : ℕ, dist p q = (n : ℝ)) → Collinear ℝ S := by
  intro S hSinf hdist
  by_contra hnc
  have htri : ∃ A ∈ S, ∃ B ∈ S, ∃ C ∈ S,
      ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    by_contra hcon
    apply hnc
    apply collinear_of_forall_triple_collinear
    intro A hA B hB C hC
    by_contra h3
    exact hcon ⟨A, hA, B, hB, C, hC, h3⟩
  obtain ⟨A, hA, B, hB, C, hC, htri⟩ := htri
  have haff : AffineIndependent ℝ ![A, B, C] := by
    rwa [collinear_iff_not_affineIndependent_set, not_not] at htri
  obtain ⟨nAB, hnAB⟩ := hdist A hA B hB
  obtain ⟨nAC, hnAC⟩ := hdist A hA C hC
  set F : Finset (ℤ × ℤ) :=
    Finset.product (Finset.Icc (-(nAB : ℤ)) nAB)
      (Finset.Icc (-(nAC : ℤ)) nAC) with hFdef
  set T : (ℤ × ℤ) → Set (EuclideanSpace ℝ (Fin 2)) := fun kv =>
    {P | dist P A - dist P B = ((kv.1 : ℤ) : ℝ) ∧
      dist P A - dist P C = ((kv.2 : ℤ) : ℝ)} with hTdef
  have hfib : ∀ kv : ℤ × ℤ, (T kv).Finite := fun kv =>
    fiber_finite A B C haff _ _
  have hsub : S ⊆ ⋃ kv ∈ (↑F : Set (ℤ × ℤ)), T kv := by
    intro P hP
    obtain ⟨nPA, hnPA⟩ := hdist P hP A hA
    obtain ⟨nPB, hnPB⟩ := hdist P hP B hB
    obtain ⟨nPC, hnPC⟩ := hdist P hP C hC
    have hleB : |dist P A - dist P B| ≤ dist A B := by
      have h := abs_dist_sub_le A B P
      rwa [dist_comm A P, dist_comm B P] at h
    have hleC : |dist P A - dist P C| ≤ dist A C := by
      have h := abs_dist_sub_le A C P
      rwa [dist_comm A P, dist_comm C P] at h
    rw [hnPA, hnPB, hnAB] at hleB
    rw [hnPA, hnPC, hnAC] at hleC
    have hcastB : ((((nPA : ℤ) - nPB : ℤ)) : ℝ)
        = (nPA : ℝ) - (nPB : ℝ) := by norm_cast
    have hcastC : ((((nPA : ℤ) - nPC : ℤ)) : ℝ)
        = (nPA : ℝ) - (nPC : ℝ) := by norm_cast
    have hkIcc : (nPA : ℤ) - nPB ∈ Finset.Icc (-(nAB : ℤ)) nAB := by
      rw [Finset.mem_Icc]
      have hmem : |((((nPA : ℤ) - nPB : ℤ)) : ℝ)| ≤ (((nAB : ℤ)) : ℝ) := by
        rw [hcastB]
        exact_mod_cast hleB
      exact_mod_cast abs_le.mp hmem
    have hvIcc : (nPA : ℤ) - nPC ∈ Finset.Icc (-(nAC : ℤ)) nAC := by
      rw [Finset.mem_Icc]
      have hmem : |((((nPA : ℤ) - nPC : ℤ)) : ℝ)| ≤ (((nAC : ℤ)) : ℝ) := by
        rw [hcastC]
        exact_mod_cast hleC
      exact_mod_cast abs_le.mp hmem
    have hmemF : ((nPA : ℤ) - nPB, (nPA : ℤ) - nPC) ∈ (↑F : Set (ℤ × ℤ)) := by
      rw [Finset.mem_coe, hFdef]
      exact Finset.mem_product.mpr ⟨hkIcc, hvIcc⟩
    refine Set.mem_biUnion hmemF ?_
    change dist P A - dist P B = (((((nPA : ℤ) - nPB : ℤ))) : ℝ) ∧
      dist P A - dist P C = (((((nPA : ℤ) - nPC : ℤ))) : ℝ)
    constructor
    · rw [hnPA, hnPB]
      norm_cast
    · rw [hnPA, hnPC]
      norm_cast
  have hfin : (⋃ kv ∈ (↑F : Set (ℤ × ℤ)), T kv).Finite :=
    (Finset.finite_toSet F).biUnion (fun kv _ => hfib kv)
  exact hSinf.not_finite (hfin.subset hsub)

end

end MetaMathlibExt
