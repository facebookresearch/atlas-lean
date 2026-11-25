/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexHornAttachment

/-! Tests for the generic horn-attachment infrastructure of
`MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexHornAttachment`:
the horn and simplex lifts into a subcomplex and its supremum
with `ofSimplex σ`, the pullback and pushout forms of the
attaching square, and extension of a map over the attached
simplex from a horn filler. These are the generic parts formerly
tested through the prism filtration in `PrismCobaseTest`, here
stated for an arbitrary simplex `σ` with horn preimage. -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped Simplicial

namespace SSet

section Signatures

#check @SSet.Subcomplex.hornLift
#check @SSet.Subcomplex.hornLift_ι
#check @SSet.Subcomplex.simplexLiftSup
#check @SSet.Subcomplex.simplexLiftSup_ι
#check @SSet.Subcomplex.hornAttach_w
#check @SSet.Subcomplex.isPullback_hornAttach
#check @SSet.Subcomplex.isPushout_hornAttach
#check @SSet.Subcomplex.exists_extension_sup_of_horn_filler

end Signatures

section AttachingHorn

variable {X : SSet.{u}} {S : X.Subcomplex} {m : ℕ} {σ : X _⦋m⦌}
  {i : Fin (m + 1)}
  (hpre : S.preimage (yonedaEquiv.symm σ) = Λ[m, i])
  (hinj : ∀ {d : ℕ} {s₁ s₂ : (Δ[m] : SSet.{u}) _⦋d⦌},
    (yonedaEquiv.symm σ).app _ s₁ =
      (yonedaEquiv.symm σ).app _ s₂ → s₁ = s₂)

/-- The horn lift really lands in `S` over the classifying map,
and the simplex lift really lands in `S ⊔ ofSimplex σ`. -/
example : Subcomplex.hornLift S σ i hpre ≫ S.ι =
    Λ[m, i].ι ≫ yonedaEquiv.symm σ :=
  Subcomplex.hornLift_ι hpre

example : Subcomplex.simplexLiftSup S σ ≫
    (S ⊔ Subcomplex.ofSimplex σ).ι = yonedaEquiv.symm σ :=
  Subcomplex.simplexLiftSup_ι

/-- The attaching square commutes, is a pullback, and (under
injectivity of the classifying map) is a pushout. -/
example : Subcomplex.hornLift S σ i hpre ≫
    Subcomplex.homOfLE le_sup_left =
    Λ[m, i].ι ≫ Subcomplex.simplexLiftSup S σ :=
  Subcomplex.hornAttach_w hpre

example : CategoryTheory.IsPullback (Subcomplex.hornLift S σ i hpre)
    Λ[m, i].ι (Subcomplex.homOfLE le_sup_left)
    (Subcomplex.simplexLiftSup S σ) :=
  Subcomplex.isPullback_hornAttach hpre

example : CategoryTheory.IsPushout (Subcomplex.hornLift S σ i hpre)
    Λ[m, i].ι (Subcomplex.homOfLE le_sup_left)
    (Subcomplex.simplexLiftSup S σ) :=
  Subcomplex.isPushout_hornAttach hpre hinj

/-- Extension step in usable form: a map out of `S` extends over
`σ` once the horn `Λ[m, i]` is filled compatibly. -/
example {C : SSet.{u}} (φ : (S : SSet.{u}) ⟶ C) (σC : Δ[m] ⟶ C)
    (hσC : Subcomplex.hornLift S σ i hpre ≫ φ = Λ[m, i].ι ≫ σC) :
    ∃ φ' : ((S ⊔ Subcomplex.ofSimplex σ : X.Subcomplex) :
        SSet.{u}) ⟶ C,
      Subcomplex.homOfLE le_sup_left ≫ φ' = φ ∧
        Subcomplex.simplexLiftSup S σ ≫ φ' = σC :=
  Subcomplex.exists_extension_sup_of_horn_filler hpre hinj φ σC hσC

end AttachingHorn

end SSet
