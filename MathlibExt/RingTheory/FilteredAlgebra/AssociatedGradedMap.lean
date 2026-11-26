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
# Maps of associated graded algebras

Let `F` and `G` be natural-number ring filtrations on `R`-algebras `A` and `B`, with
independent algebra-carrier universes. An algebra map `φ : A →ₐ[R] B` preserving each
filtration stage induces a map from the degree-`n` quotient of `F` to that of `G`, with `[a] ↦
[φ a]`.

The direct sum of these linear maps preserves the unit and multiplication, giving an
`R`-algebra map of associated graded algebras. Its action on symbols is `symbol_F(a) ↦
symbol_G(φ a)`. These maps preserve identity algebra maps and composition.
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

/-- Restriction of a filtered algebra map to each stage.

Let `φ : A →ₐ[R] B` satisfy `φ (F n) ⊆ G n` for every natural `n`. Restriction gives an
`R`-linear map `F n →ₗ[R] G n`, with underlying value `φ a`. -/
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
/-- Underlying value of a filtered stage map.

For `a : F n`, the underlying element of `stageMap F G φ hφ n a` is `φ a.val`. -/
@[simp]
theorem stageMap_coe (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n) :
    (stageMap F G φ hφ n a).val = φ a.val := rfl

omit [IsRingFiltration F (lower F)] [IsRingFiltration G (lower G)] in
/-- Filtered algebra maps preserve preceding-stage submodules.

If a representative `a : F n` lies in `lowerInStage F n`, then its image under the restricted
filtered map lies in `lowerInStage G n`. -/
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

/-- Filtered algebra map on an adjacent quotient layer.

A filtration-preserving algebra map `φ` induces an `R`-linear map `Grade F n →ₗ[R] Grade G n`
by descending its stage-`n` restriction through the preceding-stage submodules. -/
def gradeMap (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) : Grade F n →ₗ[R] Grade G n :=
  (lowerInStage F n).mapQ (lowerInStage G n) (stageMap F G φ hφ n)
    (fun a ha => stageMap_mem_lower F G φ hφ n a ha)

omit [IsRingFiltration F (lower F)] [IsRingFiltration G (lower G)] in
/-- Representative formula for the induced quotient-layer map.

The quotient class of `a : F n` maps to the quotient class of `stageMap F G φ hφ n a` in
`Grade G n`. -/
theorem gradeMap_mk (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n) :
    gradeMap F G φ hφ n ((lowerInStage F n).mkQ a) =
      (lowerInStage G n).mkQ (stageMap F G φ hφ n a) := rfl

/-- Direct-sum linear map of associated graded modules.

The induced maps `Grade F n →ₗ[R] Grade G n` assemble degree by degree to an `R`-linear map
`AssociatedGraded F →ₗ[R] AssociatedGraded G`. -/
def mapLinear (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) :
    AssociatedGraded F →ₗ[R] AssociatedGraded G :=
  DirectSum.lmap (fun n => gradeMap F G φ hφ n)

omit [IsRingFiltration F (lower F)] [IsRingFiltration G (lower G)] in
/-- Direct-sum map sends symbols to symbols of their images.

The linear associated-graded map sends `symbol F n a` to `symbol G n (stageMap F G φ hφ n a)`
for every filtered representative `a : F n`. -/
theorem mapLinear_symbol (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n) :
    mapLinear F G φ hφ (symbol F n a) = symbol G n (stageMap F G φ hφ n a) := by
  rw [symbol_mk, mapLinear, DirectSum.lmap_lof, gradeMap_mk]
  rfl

/-- Associated-graded linear map preserves the unit.

For a filtration-preserving algebra map `φ`, the induced direct-sum linear map sends the unit
of `AssociatedGraded F` to the unit of `AssociatedGraded G`. -/
theorem mapLinear_one (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) :
    mapLinear F G φ hφ 1 = 1 := by
  rw [← symbol_one F, mapLinear_symbol, ← symbol_one G]
  apply congrArg (symbol G 0)
  apply Subtype.ext
  exact φ.map_one

/-- Associated-graded linear map preserves multiplication.

For all associated-graded elements `x` and `y`, the direct-sum map induced by a filtered
algebra homomorphism satisfies `mapLinear (x * y) = mapLinear x * mapLinear y`. -/
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

/-- Algebra homomorphism induced on associated graded algebras.

A filtration-preserving algebra map `φ : A →ₐ[R] B` induces an `R`-algebra homomorphism
`AssociatedGraded F →ₐ[R] AssociatedGraded G`. Its underlying linear map is the degreewise
direct sum of quotient-layer maps. -/
def map (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) :
    AssociatedGraded F →ₐ[R] AssociatedGraded G :=
  AlgHom.ofLinearMap (mapLinear F G φ hφ) (mapLinear_one F G φ hφ)
    (mapLinear_mul F G φ hφ)

/-- Associated-graded algebra map on homogeneous symbols.

The induced algebra map sends the degree-`n` symbol of `a : F n` to the degree-`n` symbol of
its stage-restricted image under `φ`. -/
theorem map_symbol (φ : A →ₐ[R] B)
    (hφ : ∀ n (a : A), a ∈ F n → φ a ∈ G n) (n : ℕ) (a : F n) :
    map F G φ hφ (symbol F n a) = symbol G n (stageMap F G φ hφ n a) :=
  mapLinear_symbol F G φ hφ n a

/-- Identity filtered algebra map induces the identity on associated graded.

For any filtration-preservation witness of the identity map on `A`, the induced algebra map of
`AssociatedGraded F` is its identity algebra homomorphism. -/
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

/-- Associated-graded algebra maps preserve filtered composition.

For filtered algebra maps `φ : A →ₐ[R] B` and `ψ : B →ₐ[R] C`, the associated-graded map of
`ψ.comp φ` equals the composite of their associated-graded maps. The three algebra-carrier
universes are independent. -/
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
