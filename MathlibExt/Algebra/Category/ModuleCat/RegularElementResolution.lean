/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolution
public import MathlibExt.Algebra.Homology.ShortComplex.ShortExactSequences
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Regular.Defs
public meta import Lean.Elab.Tactic.Omega

/-!
# Two-term resolutions of principal right quotients

For an arbitrary ring R, left multiplication by a on the regular right module
is right-linear. Its injectivity is exactly left-regularity of a. The cokernel
is the right module R/aR, and a left-regular element gives a projective resolution
with one regular module in each of degrees zero and one and zero higher terms.

The regular right module is represented by ULift(Rᵐᵒᵖ). Taking unop coordinates
identifies its differential with x ↦ a*x and its image with aR. Ring and module
carrier universes are independent; the carrier is max(u,v).

For an arbitrary left coefficient module N, the a-annihilator is an additive
group, natural in R-linear coefficient maps. It need not be an R-submodule:
left multiplication by a on N is not asserted to be R-linear.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe u v w

namespace ModuleCat.RegularElement

variable (R : Type u) [Ring R]

/-- The regular right R-module at carrier height max(u,v), represented by
ULift(Rᵐᵒᵖ). Its right action is multiplication in unop coordinates. -/
abbrev rightRegular : ModuleCat.{max u v} Rᵐᵒᵖ :=
  ModuleCat.of Rᵐᵒᵖ (ULift.{v, u} Rᵐᵒᵖ)

/-- Left multiplication by a on the regular right module. In opposite
coordinates it is right multiplication by op(a), so no centrality is required. -/
def leftMultiplication (a : R) : rightRegular.{u, v} R ⟶ rightRegular.{u, v} R :=
  ModuleCat.ofHom
    { toFun x := ULift.up (x.down * MulOpposite.op a)
      map_add' x y := by
        apply ULift.ext
        exact add_mul x.down y.down (MulOpposite.op a)
      map_smul' r x := by
        apply ULift.ext
        change (r * x.down) * MulOpposite.op a = r * (x.down * MulOpposite.op a)
        exact mul_assoc r x.down (MulOpposite.op a) }

/-- The differential is multiplication by a on the left in the original ring. -/
@[simp]
theorem leftMultiplication_unop_apply (a : R) (x : rightRegular.{u, v} R) :
    ((leftMultiplication.{u, v} R a).hom x).down.unop = a * x.down.unop :=
  rfl

/-- A left-regular ring element gives an injective right-module differential. -/
theorem leftMultiplication_injective (a : R) (ha : IsLeftRegular a) :
    Function.Injective (leftMultiplication.{u, v} R a).hom := by
  intro x y h
  apply ULift.ext
  apply MulOpposite.unop_injective
  apply ha
  exact congrArg (fun z : rightRegular.{u, v} R => z.down.unop) h

/-- Monicity of the regular right-module differential is exactly left-regularity. -/
theorem leftMultiplication_mono_iff (a : R) :
    Mono (leftMultiplication.{u, v} R a) ↔ IsLeftRegular a := by
  rw [ModuleCat.mono_iff_injective]
  constructor
  · intro h x y hxy
    have h' :
        (leftMultiplication.{u, v} R a).hom (ULift.up (MulOpposite.op x)) =
          (leftMultiplication.{u, v} R a).hom (ULift.up (MulOpposite.op y)) := by
      apply ULift.ext
      apply MulOpposite.unop_injective
      exact hxy
    exact congrArg (fun z : rightRegular.{u, v} R => z.down.unop) (h h')
  · exact leftMultiplication_injective.{u, v} R a

/-- The principal right ideal aR, represented inside the lifted regular right module. -/
def principalRightIdeal (a : R) : Submodule Rᵐᵒᵖ (rightRegular.{u, v} R) :=
  (leftMultiplication.{u, v} R a).hom.range

/-- Membership in the differential image is the equation x = a*r in unop coordinates. -/
theorem mem_principalRightIdeal_iff (a : R) (x : rightRegular.{u, v} R) :
    x ∈ principalRightIdeal.{u, v} R a ↔ ∃ r : R, a * r = x.down.unop := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.down.unop,
      congrArg (fun z : rightRegular.{u, v} R => z.down.unop) hy⟩
  · rintro ⟨r, hr⟩
    refine ⟨ULift.up (MulOpposite.op r), ?_⟩
    apply ULift.ext
    apply MulOpposite.unop_injective
    exact hr

/-- The cyclic right quotient R/aR at the selected carrier height. -/
abbrev quotient (a : R) : ModuleCat.{max u v} Rᵐᵒᵖ :=
  cokernel (leftMultiplication.{u, v} R a)

/-- The cyclic quotient agrees with the concrete quotient by the principal right ideal. -/
def quotientIsoRange (a : R) :
    quotient.{u, v} R a ≅
      ModuleCat.of Rᵐᵒᵖ (rightRegular.{u, v} R ⧸ principalRightIdeal.{u, v} R a) :=
  ModuleCat.cokernelIsoRangeQuotient (leftMultiplication.{u, v} R a)

/-- The regular-module presentation of the cyclic right quotient. -/
abbrev sequence (a : R) : ShortComplex (ModuleCat.{max u v} Rᵐᵒᵖ) :=
  ShortComplex.cokernelSequence (leftMultiplication.{u, v} R a)

/-- Left-regularity makes the principal right-quotient presentation short exact. -/
theorem sequence_shortExact (a : R) (ha : IsLeftRegular a) :
    (sequence.{u, v} R a).ShortExact := by
  letI : Mono (leftMultiplication.{u, v} R a) :=
    (leftMultiplication_mono_iff.{u, v} R a).mpr ha
  exact ShortComplex.shortExact_cokernelSequence (leftMultiplication.{u, v} R a)

/-- The regular-module presentation gives a finite two-term resolution. -/
def finiteResolution (a : R) (ha : IsLeftRegular a) :
    CategoryTheory.Abelian.FiniteResolution
      (𝟭 (ModuleCat.{max u v} Rᵐᵒᵖ)) (quotient.{u, v} R a) :=
  CategoryTheory.Abelian.FiniteResolution.ofShortExact
    (rightRegular.{u, v} R) (leftMultiplication.{u, v} R a)
    (cokernel.π (leftMultiplication.{u, v} R a))
    (cokernel.condition (leftMultiplication.{u, v} R a))
    (sequence_shortExact.{u, v} R a ha)
    (CategoryTheory.Abelian.FiniteResolution.single
      (𝟭 (ModuleCat.{max u v} Rᵐᵒᵖ)) (rightRegular.{u, v} R))

/-- The resolution has support bound one. -/
@[simp]
theorem finiteResolution_bound (a : R) (ha : IsLeftRegular a) :
    (finiteResolution.{u, v} R a ha).bound = 1 :=
  rfl

/-- The degree-zero resolving object is the regular right module. -/
@[simp]
theorem finiteResolution_X_zero (a : R) (ha : IsLeftRegular a) :
    (finiteResolution.{u, v} R a ha).mappedComplex.X 0 = rightRegular.{u, v} R :=
  rfl

/-- The degree-one resolving object is the regular right module. -/
@[simp]
theorem finiteResolution_X_one (a : R) (ha : IsLeftRegular a) :
    (finiteResolution.{u, v} R a ha).mappedComplex.X 1 = rightRegular.{u, v} R :=
  rfl

/-- The constructed finite resolution is degreewise projective, using the two
free regular modules and the zero objects in every higher degree. -/
def projectiveResolution (a : R) (ha : IsLeftRegular a) :
    ProjectiveResolution (quotient.{u, v} R a) where
  complex := (finiteResolution.{u, v} R a ha).mappedComplex
  projective n := by
    rcases n with (_ | _ | n)
    · change Projective (rightRegular.{u, v} R)
      infer_instance
    · change Projective (rightRegular.{u, v} R)
      infer_instance
    · exact ((finiteResolution.{u, v} R a ha).mappedComplex_isZero_above
        (n + 2) (by rw [finiteResolution_bound]; omega)).projective
  π := (finiteResolution.{u, v} R a ha).augmentation
  quasiIso := (finiteResolution.{u, v} R a ha).quasiIso

/-- The differential of the projective resolution is the original right-linear
left multiplication map. -/
theorem projectiveResolution_d_one_zero (a : R) (ha : IsLeftRegular a) :
    (projectiveResolution.{u, v} R a ha).complex.d 1 0 =
      leftMultiplication.{u, v} R a := by
  let Q := CategoryTheory.Abelian.FiniteResolution.single
    (𝟭 (ModuleCat.{max u v} Rᵐᵒᵖ)) (rightRegular.{u, v} R)
  have h := CategoryTheory.Abelian.FiniteResolution.ofShortExact_mappedComplex_d_one_zero
    (rightRegular.{u, v} R) (leftMultiplication.{u, v} R a)
    (cokernel.π (leftMultiplication.{u, v} R a))
    (cokernel.condition (leftMultiplication.{u, v} R a))
    (sequence_shortExact.{u, v} R a ha) Q
  have hQ : Q.augmentation₀ = 𝟙 (rightRegular.{u, v} R) := by
    change ((HomologicalComplex.singleMapHomologicalComplex
      (𝟭 (ModuleCat.{max u v} Rᵐᵒᵖ)) (ComplexShape.down ℕ) 0).hom.app
        (rightRegular.{u, v} R)).f 0 = 𝟙 _
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
      Functor.id_map, Category.id_comp]
  rw [hQ, Category.id_comp] at h
  exact h

/-- Every term above degree one in the projective resolution is zero. -/
theorem projectiveResolution_isZero_above (a : R) (ha : IsLeftRegular a)
    (n : ℕ) (hn : 1 < n) :
    IsZero ((projectiveResolution.{u, v} R a ha).complex.X n) :=
  (finiteResolution.{u, v} R a ha).mappedComplex_isZero_above n
    (by simpa only [finiteResolution_bound] using hn)

/-- Multiplication by a on a left coefficient is additive, without any centrality
or coefficient-flatness condition. -/
def coefficientAction (a : R) (N : ModuleCat.{w} R) : N →+ N where
  toFun n := a • n
  map_zero' := smul_zero a
  map_add' := smul_add a

/-- The additive group of coefficients annihilated by a. -/
abbrev annihilatorGroup (a : R) (N : ModuleCat.{w} R) : AddCommGrpCat.{w} :=
  AddCommGrpCat.of (coefficientAction R a N).ker

/-- An R-linear coefficient map preserves the a-annihilator additive group. -/
def annihilatorMap (a : R) {N N' : ModuleCat.{w} R} (g : N ⟶ N') :
    annihilatorGroup R a N ⟶ annihilatorGroup R a N' :=
  AddCommGrpCat.ofHom
    { toFun n := ⟨g.hom n.val, by
        have hn : a • n.val = 0 := n.property
        change a • g.hom n.val = 0
        rw [← g.hom.map_smul, hn, map_zero]⟩
      map_zero' := by
        apply Subtype.ext
        exact g.hom.map_zero
      map_add' x y := by
        apply Subtype.ext
        exact g.hom.map_add x.val y.val }

end ModuleCat.RegularElement
