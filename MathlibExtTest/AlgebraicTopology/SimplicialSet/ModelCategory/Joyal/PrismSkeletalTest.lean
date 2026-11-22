/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.PrismSkeletal

/-!
# PrismSkeletalTest
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

section Signatures

variable {A B C D X Y : SSet.{u}} {i : A ⟶ B} [Mono i] {κ : Fin 2}
  [Quasicategory C]


end Signatures

section Closures

variable {A B C : SSet.{u}} (i : A ⟶ B) [Mono i] [Quasicategory C]
  {κ : Fin 2} {n d : ℕ}

/-- The monomorphism case at a boundary inclusion has the
cell statement, at either vertex. -/
example : PrismOneExtensionAt κ ∂Δ[n].ι C :=
  prismOneExtensionAt_of_mono κ ∂Δ[n].ι

/-- Source form of the monomorphism case at a boundary
inclusion. -/
example : PrismSrcExtension ∂Δ[3].ι C :=
  prismSrcExtension_of_mono ∂Δ[3].ι

/-- Target form of the monomorphism case at a boundary
inclusion. -/
example : PrismTgtExtension ∂Δ[3].ι C :=
  prismTgtExtension_of_mono ∂Δ[3].ι

/-- `Δ[1]` extension along a general monomorphism, source
and target forms. -/
example : PrismSrcExtension i C ∧ PrismTgtExtension i C :=
  ⟨prismSrcExtension_of_mono i, prismTgtExtension_of_mono i⟩

/-- One skeleton step of a monomorphism, directly. -/
example : PrismOneExtensionAt κ (relativeCellComplexOfMono.r i d) C :=
  prismOneExtensionAt_skeletonStep i d

/-- Composition closure instance: two boundary-step maps
composed. -/
example {D : SSet.{u}} (j : B ⟶ D)
    (hi : PrismOneExtensionAt κ i C) (hj : PrismOneExtensionAt κ j C) :
    PrismOneExtensionAt κ (i ≫ j) C :=
  hi.comp hj

/-- Coproduct closure instance: constantly the same cell. -/
example : PrismOneExtensionAt κ
    (Limits.Sigma.map (fun _ : ULift.{u} (Fin 2) ↦
      (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ (Δ[n] : SSet.{u})))) C :=
  PrismOneExtensionAt.sigmaMap
    (fun _ ↦ prismOneExtensionAt_boundary κ)

end Closures

section ShuffleHypotheses

variable {A B C : SSet.{u}} (i : A ⟶ B) [Mono i] [Quasicategory C]
  (hcell0 : ∀ n, ShuffleHornZeroCellExtension n C)
  (hcell2 : ∀ n, ShuffleHornTwoCellExtension n C) {d : ℕ}

/-- Horn-zero extension along a monomorphism from the cell
hypotheses. -/
example : PrismTwoHornZeroExtension i C :=
  prismTwoHornZeroExtension_of_mono_of_shuffleCell i hcell0

/-- Horn-two extension along a monomorphism from the cell
hypotheses. -/
example : PrismTwoHornTwoExtension i C :=
  prismTwoHornTwoExtension_of_mono_of_shuffleCell i hcell2

/-- One skeleton step, horn zero, from the cell hypotheses. -/
example : PrismTwoHornZeroExtension
    (relativeCellComplexOfMono.r i d) C :=
  prismTwoHornZeroExtension_skeletonStep i hcell0 d

/-- (A) in conditional form. -/
example : HoPrePrismStrictExtension i C :=
  hoPrePrismStrictExtension_of_mono_of_shuffleCell i C hcell0 hcell2

/-- The isofibration conclusion in conditional form. -/
example : (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration :=
  hoFunctor_pre_isIsofibration_of_mono_of_shuffleCell i C hcell0 hcell2

end ShuffleHypotheses

section Values

/-- The `δ₂`-face of `Λ[2,0]` has value the `(0 ⟶ 1)`-edge. -/
example : (horn.face (0 : Fin 3) (2 : Fin 3) (by decide)).val =
    shuffleEdge01 :=
  horn_face_zero_two_val

/-- The `δ₀`-face of `Λ[2,2]` has value the `(1 ⟶ 2)`-edge. -/
example : (horn.face (2 : Fin 3) (0 : Fin 3) (by decide)).val =
    shuffleEdge12 :=
  horn_face_two_zero_val

/-- The whiskered horn face inclusion at the vertex `0` of
`Δ[1]`, as a horn vertical simplex. -/
example : (Δ[1] ◁ horn.ι (0 : Fin 3) (2 : Fin 3) (by decide)).app _
      (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)) =
    hornVertZeroSimplex (stdSimplex.obj₀Equiv.symm 0) :=
  whiskerLeft_horn_ι_zero_app_vertical _

/-- `δ₁δ₀ = δ₀δ₂` on the fundamental simplex of `Δ[2]`. -/
example : (Δ[2] : SSet.{u}).δ 1
      ((Δ[2] : SSet.{u}).δ 0 (yonedaEquiv (𝟙 (Δ[2] : SSet.{u})))) =
    (Δ[2] : SSet.{u}).δ 0
      ((Δ[2] : SSet.{u}).δ 2 (yonedaEquiv (𝟙 (Δ[2] : SSet.{u})))) :=
  delta_one_delta_zero_apply _

/-- Every `κ : Fin 2` is `0` or `1`. -/
example (κ : Fin 2) : κ = 0 ∨ κ = 1 :=
  fin_two_eq_zero_or_one κ

end Values

end SSet
