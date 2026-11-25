/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.RingTheory.FilteredAlgebra.AssociatedGraded

/-!
# Actual maps of associated graded algebras

A filtered algebra homomorphism induces the original map on every adjacent
quotient and the native map of their external direct sums. The product and
unit laws follow from the actual representative formulas, so the result is
an algebra map before any PBW or projectivity hypothesis is considered.
-/

@[expose] public section

noncomputable section

universe u v w w'

namespace FilteredAlgebra

variable {R : Type u} [CommRing R]
  {A : Type v} [Ring A] [Algebra R A]
  {B : Type w} [Ring B] [Algebra R B]
  {C : Type w'} [Ring C] [Algebra R C]
  (F : ℕ → Submodule R A) [IsRingFiltration F (lower F)]
  (G : ℕ → Submodule R B) [IsRingFiltration G (lower G)]

/-- Restrict a filtered algebra map to the original filtration-stage carriers. -/
def stageMap (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) : F n →ₗ[R] G n where
  toFun a := ⟨φ a.val, hφ n a.val a.property⟩
  map_add' a b := by
    apply Subtype.ext
    exact φ.map_add a.val b.val
  map_smul' r a := by
    apply Subtype.ext
    exact φ.toLinearMap.map_smul r a.val

omit [IsRingFiltration F (lower F)] [IsRingFiltration G (lower G)] in
@[simp]
theorem stageMap_coe (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n) :
    (stageMap F G φ hφ n a).val = φ a.val := rfl

omit [IsRingFiltration F (lower F)] [IsRingFiltration G (lower G)] in
theorem stageMap_mem_lower (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n)
    (ha : a ∈ lowerInStage F n) : stageMap F G φ hφ n a ∈ lowerInStage G n := by
  cases n with
  | zero =>
      have ha0 : a = 0 := (Submodule.mem_bot R).mp ha
      rw [ha0, map_zero]
      exact (lowerInStage G 0).zero_mem
  | succ n =>
      change φ a.val ∈ G n
      exact hφ n a.val ha

/-- The map on original adjacent quotient layers. -/
def gradeMap (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) : Grade F n →ₗ[R] Grade G n :=
  (lowerInStage F n).mapQ (lowerInStage G n) (stageMap F G φ hφ n)
    (fun a ha => stageMap_mem_lower F G φ hφ n a ha)

omit [IsRingFiltration F (lower F)] [IsRingFiltration G (lower G)] in
theorem gradeMap_mk (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n) :
    gradeMap F G φ hφ n ((lowerInStage F n).mkQ a) =
      (lowerInStage G n).mkQ (stageMap F G φ hφ n a) := rfl

/-- The actual native direct-sum map of quotient layers. -/
def mapLinear (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) :
    AssociatedGraded F →ₗ[R] AssociatedGraded G :=
  DirectSum.lmap (fun n => gradeMap F G φ hφ n)

omit [IsRingFiltration F (lower F)] [IsRingFiltration G (lower G)] in
theorem mapLinear_symbol (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n) :
    mapLinear F G φ hφ (symbol F n a) = symbol G n (stageMap F G φ hφ n a) := by
  rw [symbol_mk, mapLinear, DirectSum.lmap_lof, gradeMap_mk]
  rfl

theorem mapLinear_one (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) :
    mapLinear F G φ hφ 1 = 1 := by
  rw [← symbol_one F, mapLinear_symbol, ← symbol_one G]
  apply congrArg (symbol G 0)
  apply Subtype.ext
  exact φ.map_one

theorem mapLinear_mul (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n)
    (x y : AssociatedGraded F) :
    mapLinear F G φ hφ (x * y) = mapLinear F G φ hφ x * mapLinear F G φ hφ y := by
  have h : ∀ x : AssociatedGraded F, ∀ y : AssociatedGraded F,
      mapLinear F G φ hφ (x * y) = mapLinear F G φ hφ x * mapLinear F G φ hφ y := by
    intro x
    refine symbol_induction F ?_ ?_ ?_ x
    · intro y
      rw [zero_mul, map_zero, zero_mul]
    · intro n u y
      refine symbol_induction F ?_ ?_ ?_ y
      · rw [mul_zero, map_zero, mul_zero]
      · intro m v
        rw [symbol_mul, mapLinear_symbol, mapLinear_symbol, mapLinear_symbol, symbol_mul]
        apply congrArg (symbol G (n + m))
        apply Subtype.ext
        exact φ.map_mul u.val v.val
      · intro y z hy hz
        rw [mul_add, map_add, hy, hz, map_add, mul_add]
    · intro x y hx hy z
      rw [add_mul, map_add, hx z, hy z, map_add, add_mul]
  exact h x y

/-- A filtered algebra map induces the actual algebra map of associated gradeds. -/
def map (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) :
    AssociatedGraded F →ₐ[R] AssociatedGraded G :=
  AlgHom.ofLinearMap (mapLinear F G φ hφ) (mapLinear_one F G φ hφ)
    (mapLinear_mul F G φ hφ)

theorem map_symbol (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n) :
    map F G φ hφ (symbol F n a) = symbol G n (stageMap F G φ hφ n a) :=
  mapLinear_symbol F G φ hφ n a

/-- The map on original quotient layers preserves identities. -/
@[simp]
theorem map_id
    (h : ∀ n (a : A), a ∈ F n → (AlgHom.id R A) a ∈ F n) :
    map F F (AlgHom.id R A) h = AlgHom.id R (AssociatedGraded F) := by
  apply DFunLike.ext
  intro x
  refine symbol_induction F ?_ ?_ ?_ x
  · simp only [map_zero]
  · intro n u
    rw [map_symbol]
    apply congrArg (symbol F n)
    apply Subtype.ext
    rfl
  · intro x y hx hy
    simp only [map_add, hx, hy]

variable (H : ℕ → Submodule R C) [IsRingFiltration H (lower H)]

/-- The actual quotient/direct-sum maps preserve composition across independent
algebra-carrier universes. -/
theorem map_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n)
    (hψ : ∀ n (b : B), b ∈ G n → ψ b ∈ H n) :
    map F H (ψ.comp φ) (fun n a ha => hψ n (φ a) (hφ n a ha)) =
      (map G H ψ hψ).comp (map F G φ hφ) := by
  apply DFunLike.ext
  intro x
  refine symbol_induction F ?_ ?_ ?_ x
  · simp only [map_zero, AlgHom.comp_apply]
  · intro n u
    have hLeft := map_symbol F H (ψ.comp φ)
      (fun n a ha => hψ n (φ a) (hφ n a ha)) n u
    have hFirst := map_symbol F G φ hφ n u
    have hSecond := map_symbol G H ψ hψ n (stageMap F G φ hφ n u)
    have hStage : stageMap F H (ψ.comp φ)
        (fun n a ha => hψ n (φ a) (hφ n a ha)) n u =
      stageMap G H ψ hψ n (stageMap F G φ hφ n u) := Subtype.ext rfl
    exact hLeft.trans ((congrArg (symbol H n) hStage).trans
      ((hSecond.symm.trans (congrArg (map G H ψ hψ) hFirst.symm))))
  · intro x y hx hy
    simp only [map_add, AlgHom.comp_apply, hx, hy]

end FilteredAlgebra
