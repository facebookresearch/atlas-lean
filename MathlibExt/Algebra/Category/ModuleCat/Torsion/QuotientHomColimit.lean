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

public import MathlibExt.LinearAlgebra.Quotient.IdealHom
public import MathlibExt.Algebra.Category.ModuleCat.TorsionAnnihilatorColimit
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Power torsion as a colimit of quotient Hom modules

Let `R : Type u` be a commutative ring and `I` an ideal. For `M : ModuleCat.{u} R`, evaluation
at the class of one identifies `Hom_R(R / I^n, M)` with the submodule annihilated by every
element of `I^n`.

If `n ≤ m`, the quotient map `R / I^m → R / I^n` induces the transition map by precomposition.
Under evaluation, this is the inclusion of the power annihilators. The resulting natural-
number diagram has colimit the power-torsion module `Γ_I(M)`, consisting of elements
annihilated by some ideal power.

The evaluation cocone and its colimit isomorphism are natural in module maps. The quotient-Hom
diagrams here use the ring's carrier universe `u`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace ModuleCat.Torsion

variable {R : Type u} [CommRing R]

/-- Quotient module by an ideal power.

For natural `n`, `quotientPowerModule I n` is the `R`-module `R / I^n`, bundled in
`ModuleCat.{u} R`. -/
@[implicit_reducible]
def quotientPowerModule (I : Ideal R) (n : ℕ) : ModuleCat.{u} R :=
  (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).obj (op n)

/-- Increasing family of Hom functors from ideal-power quotients.

The natural-number family has degree-`n` functor `Hom_R(R / I^n, -)`. For `n ≤ m`, its natural
transformation is precomposition with the quotient map `R / I^m → R / I^n`. -/
@[implicit_reducible]
def quotientHomFamily (I : Ideal R) : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  opOp ℕ ⋙
    (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).op ⋙
      linearCoyoneda R (ModuleCat.{u} R)

local instance (I : Ideal R) (n : ℕ) : ((quotientHomFamily I).obj n).Additive := by
  change ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (quotientPowerModule I n))).Additive
  infer_instance

/-- Ideal-power quotient Hom family as additive functors.

Bundle each functor `Hom_R(R / I^n, -)` with its additivity and retain the precomposition
transition maps to form a natural-number family of additive functors. -/
def quotientHomAdditiveFamily (I : Ideal R) :
    ℕ ⥤ (ModuleCat.{u} R ⥤+ ModuleCat.{u} R) where
  obj n := AdditiveFunctor.of ((quotientHomFamily I).obj n)
  map f := ⟨(quotientHomFamily I).map f⟩
  map_id n := by
    apply ObjectProperty.hom_ext
    exact (quotientHomFamily I).map_id n
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (quotientHomFamily I).map_comp f g

/-- Module functor to ideal-power quotient Hom diagrams.

For an `R`-module `M`, take the diagram `n ↦ Hom_R(R / I^n, M)`. Module maps act on the
diagram by postcomposition. -/
@[implicit_reducible]
def quotientHomDiagramFunctor (I : Ideal R) :
    ModuleCat.{u} R ⥤ (ℕ ⥤ ModuleCat.{u} R) :=
  (quotientHomFamily I).flip

/-- Quotient Hom diagram of a fixed module.

The diagram for `I` and `M` has objects `Hom_R(R / I^n, M)` and transition maps induced by the
quotient projections between ideal-power quotients. -/
@[implicit_reducible]
def quotientHomDiagram (I : Ideal R) (M : ModuleCat.{u} R) : ℕ ⥤ ModuleCat.{u} R :=
  (quotientHomDiagramFunctor I).obj M

/-- Evaluation identifies quotient Hom with the power-annihilator diagram.

Evaluation at the quotient class of one gives a natural isomorphism from `quotientHomDiagram I
M` to the diagram of submodules annihilated by `I^n`. It turns quotient precomposition into
the annihilator inclusions. -/
def quotientHomDiagramIsoAnnihilator (I : Ideal R) (M : ModuleCat.{u} R) :
    quotientHomDiagram I M ≅ annihilatorDiagram I M :=
  NatIso.ofComponents
    (fun n =>
      ((ModuleCat.homLinearEquiv (S := R) (M := quotientPowerModule I n) (N := M)).trans
        (Ideal.quotientHomEquiv (I ^ n) (M : Type u))).toModuleIso)
    (by
      intro i j f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      rfl)

/-- Quotient Hom and annihilator diagram comparison is natural in modules.

The evaluation isomorphisms assemble to a natural isomorphism between the module-valued
quotient-Hom diagram functor and the power-annihilator diagram functor. -/
def quotientHomDiagramFunctorIsoAnnihilator (I : Ideal R) :
    quotientHomDiagramFunctor I ≅ annihilatorDiagramFunctor I :=
  NatIso.ofComponents (quotientHomDiagramIsoAnnihilator I) (by
    intro M N f
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    rfl)

/-- Evaluation cocone from quotient Hom to power torsion.

The cocone on `n ↦ Hom_R(R / I^n, M)` has point `Γ_I(M)` and sends a quotient-module map to
its value on the class of one, included as a power-torsion element. -/
def quotientHomCocone (I : Ideal R) (M : ModuleCat.{u} R) :
    Cocone (quotientHomDiagram I M) :=
  (Cocone.precompose (quotientHomDiagramIsoAnnihilator I M).hom).obj
    (annihilatorCocone I M)

/-- Underlying value of a quotient Hom cocone map.

For `φ : R / I^n ⟶ M`, the degree-`n` cocone map has underlying value `φ(1 mod I^n)`. -/
lemma quotientHomCocone_val (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (φ : quotientPowerModule I n ⟶ M) :
    (((quotientHomCocone I M).ι.app n).hom φ).val =
      φ.hom (Ideal.quotientOne (I ^ n)) := rfl

/-- Power torsion is the colimit of ideal-power quotient Hom.

The evaluation cocone with point `Γ_I(M)` is a colimit cocone of `quotientHomDiagram I M`. -/
def quotientHomIsColimit (I : Ideal R) (M : ModuleCat.{u} R) :
    IsColimit (quotientHomCocone I M) :=
  (IsColimit.precomposeHomEquiv (quotientHomDiagramIsoAnnihilator I M)
    (annihilatorCocone I M)).symm (annihilatorIsColimit I M)

/-- Evaluation cocone commutes with module coefficient maps.

For `f : M ⟶ N`, evaluation into `Γ_I(M)` followed by the power-torsion map of `f` equals
postcomposition by `f` in the quotient Hom diagram followed by evaluation into `Γ_I(N)`. -/
lemma quotientHom_coefficient_naturality (I : Ideal R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (n : ℕ) :
    (quotientHomCocone I M).ι.app n ≫ (functor I).map f =
      ((quotientHomDiagramFunctor I).map f).app n ≫ (quotientHomCocone I N).ι.app n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

/-- Power-torsion module as the quotient Hom colimit object.

The evaluation colimit gives an isomorphism `Γ_I(M) ≅ colimit (quotientHomDiagram I M)`. -/
def gammaIsoQuotientHomColimitObj (I : Ideal R) (M : ModuleCat.{u} R) :
    (functor I).obj M ≅ colimit (quotientHomDiagram I M) :=
  (quotientHomIsColimit I M).coconePointUniqueUpToIso
    (colimit.isColimit (quotientHomDiagram I M))

/-- Power-torsion colimit isomorphism sends evaluation to the colimit injection.

The degree-`n` evaluation cocone map followed by the forward power-torsion colimit isomorphism
equals the colimit injection at `n`. -/
lemma quotientHomCocone_comp_gammaIso_hom (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (quotientHomCocone I M).ι.app n ≫ (gammaIsoQuotientHomColimitObj I M).hom =
      colimit.ι (quotientHomDiagram I M) n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (quotientHomIsColimit I M) (colimit.isColimit (quotientHomDiagram I M)) n

/-- Inverse power-torsion colimit isomorphism recovers evaluation.

The colimit injection at `n` followed by the inverse power-torsion colimit isomorphism equals
the quotient Hom evaluation cocone map. -/
lemma colimit_iota_comp_gammaIso_inv (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    colimit.ι (quotientHomDiagram I M) n ≫ (gammaIsoQuotientHomColimitObj I M).inv =
      (quotientHomCocone I M).ι.app n :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (quotientHomIsColimit I M) (colimit.isColimit (quotientHomDiagram I M)) n

/-- Power torsion is naturally the colimit of its quotient Hom diagram.

The objectwise evaluation colimit isomorphisms give a natural isomorphism from the power-
torsion functor to the quotient-Hom diagram functor followed by colimit. -/
def gammaIsoQuotientHomColimit (I : Ideal R) :
    (functor I : ModuleCat.{u} R ⥤ ModuleCat.{u} R) ≅ quotientHomDiagramFunctor I ⋙ colim :=
  NatIso.ofComponents (gammaIsoQuotientHomColimitObj I) (by
    intro M N f
    apply (quotientHomIsColimit I M).hom_ext
    intro n
    let iM := (quotientHomCocone I M).ι.app n
    let iN := (quotientHomCocone I N).ι.app n
    let d := ((quotientHomDiagramFunctor I).map f).app n
    let eM := gammaIsoQuotientHomColimitObj I M
    let eN := gammaIsoQuotientHomColimitObj I N
    have hM : iM ≫ eM.hom = colimit.ι (quotientHomDiagram I M) n :=
      quotientHomCocone_comp_gammaIso_hom I M n
    have hN : iN ≫ eN.hom = colimit.ι (quotientHomDiagram I N) n :=
      quotientHomCocone_comp_gammaIso_hom I N n
    have hf : iM ≫ (functor I).map f = d ≫ iN :=
      quotientHom_coefficient_naturality I f n
    have hc : colimit.ι (quotientHomDiagram I M) n ≫
        colim.map ((quotientHomDiagramFunctor I).map f) =
          d ≫ colimit.ι (quotientHomDiagram I N) n :=
      colimit.ι_map ((quotientHomDiagramFunctor I).map f) n
    calc
      iM ≫ ((functor I).map f ≫ eN.hom) = (iM ≫ (functor I).map f) ≫ eN.hom :=
        (Category.assoc _ _ _).symm
      _ = (d ≫ iN) ≫ eN.hom := congrArg (fun g => g ≫ eN.hom) hf
      _ = d ≫ (iN ≫ eN.hom) := Category.assoc _ _ _
      _ = d ≫ colimit.ι (quotientHomDiagram I N) n := congrArg (fun g => d ≫ g) hN
      _ = colimit.ι (quotientHomDiagram I M) n ≫
          colim.map ((quotientHomDiagramFunctor I).map f) := hc.symm
      _ = (iM ≫ eM.hom) ≫ colim.map ((quotientHomDiagramFunctor I).map f) :=
        congrArg (fun g => g ≫ colim.map ((quotientHomDiagramFunctor I).map f)) hM.symm
      _ = iM ≫ (eM.hom ≫ colim.map ((quotientHomDiagramFunctor I).map f)) :=
        Category.assoc _ _ _)

end ModuleCat.Torsion
