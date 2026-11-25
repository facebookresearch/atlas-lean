/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
public import MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
public import MathlibExt.AlgebraicGeometry.DerivedLinearClosingPaths

/-!
# Source-normalized derived-intersection closing-data paths

The universal path is the actual second projection of the native
derived fibre. The NC path model factors the actual diagonal restriction
through a trivial cochain fibration. Both endpoint sections and the
universal fibre comparison are fixed by actual NC pullbacks. Its
homotopy is the computed relative cylinder lift, not an independent
closing path. A source constructor chooses the coupled native models.

Reference: PTVV1111.3209v4 Theorem2.9, pp39--40.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedFibreClosingPaths

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
open MathlibExt.AlgebraicGeometry.DerivedLinearClosingPaths
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.RelativeCochainHomotopies
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {NC : NegativeCyclicDiagram D.functor (2 : ℤ)}

/-- The true natural path carried by every derived-fibre simplex. -/
def universalPath {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} (Z : FibreStackModel P f g) :
    Z.stack.functor ⟶ P.P := eqToHom Z.functor_eq ≫ pullback.snd _ _

/-- The actual shifted NC pullback used by a degree-n closing path. -/
def shiftedNCMap {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D 2 NC Y) (GX : GlobalNCModel D 2 NC X) (n : ℤ) :
    (ncComplex GY)⟦n - ((2 : ℕ) : ℤ)⟧ ⟶ (ncComplex GX)⟦n - ((2 : ℕ) : ℤ)⟧ :=
  (shiftFunctor (GlobalComplex k) (n - ((2 : ℕ) : ℤ))).map (ncPullback f GY GX)

/-- Closing-data pullback is literally realization of the same shifted cochain pullback. -/
theorem closedPullback_eq_realize_shiftedNC {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D 2 NC Y) (GX : GlobalNCModel D 2 NC X) (n : ℤ) :
    closedPullback f GY GX n = (realize k).map (shiftedNCMap f GY GX n) := rfl

/-- The coupled native models retain the actual relative path projection and fibre squares. -/
structure FibreNCPathModel {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} (Z : FibreStackModel P f g)
    (GF : GlobalNCModel D 2 NC F.functor) (GX : GlobalNCModel D 2 NC X.functor)
    (GY : GlobalNCModel D 2 NC Y.functor) (GP : GlobalNCModel D 2 NC P.P)
    (GZ : GlobalNCModel D 2 NC Z.stack.functor) (n : ℤ) where
  path : GlobalComplex k
  augmentation : (ncComplex GP)⟦n - ((2 : ℕ) : ℤ)⟧ ⟶ path
  augmentation_mono : Mono augmentation
  augmentation_weak : QuasiIso augmentation
  projection : path ⟶ (ncComplex GF)⟦n - ((2 : ℕ) : ℤ)⟧
  normalized : augmentation ≫ projection = shiftedNCMap P.ι GP GF n
  fibration : IsTrivialMonoFibration projection
  first_section : (shiftedNCMap P.p₀ GF GP n ≫ augmentation) ≫ projection = 𝟙 _
  second_section : (shiftedNCMap P.p₁ GF GP n ≫ augmentation) ≫ projection = 𝟙 _
  fibre : path ⟶ (ncComplex GZ)⟦n - ((2 : ℕ) : ℤ)⟧
  fibre_normalized : augmentation ≫ fibre = shiftedNCMap (universalPath Z) GP GZ n
  first_square : (shiftedNCMap P.p₀ GF GP n ≫ augmentation) ≫ fibre =
    shiftedNCMap f GF GX n ≫ shiftedNCMap (DerivedStackFibreModels.first Z) GX GZ n
  second_square : (shiftedNCMap P.p₁ GF GP n ≫ augmentation) ≫ fibre =
    shiftedNCMap g GF GY n ≫ shiftedNCMap (DerivedStackFibreModels.second Z) GY GZ n
  first_realization_square :
    (realize k).map (shiftedNCMap P.p₀ GF GP n ≫ augmentation) ≫ (realize k).map fibre =
      closedPullback f GF GX n ≫ closedPullback (DerivedStackFibreModels.first Z) GX GZ n
  second_realization_square :
    (realize k).map (shiftedNCMap P.p₁ GF GP n ≫ augmentation) ≫ (realize k).map fibre =
      closedPullback g GF GY n ≫ closedPullback (DerivedStackFibreModels.second Z) GY GZ n

/-- The actual first cochain endpoint section. -/
def FibreNCPathModel.firstEndpoint {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) := shiftedNCMap P.p₀ GF GP n ≫ C.augmentation

/-- The actual second cochain endpoint section. -/
def FibreNCPathModel.secondEndpoint {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) := shiftedNCMap P.p₁ GF GP n ≫ C.augmentation

/-- The path homotopy is the actual native lift of the relative cylinder square. -/
def FibreNCPathModel.homotopy {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) :=
  relativeHomotopy C.projection C.fibration C.firstEndpoint C.secondEndpoint
    C.first_section C.second_section

/-- The comparison homotopy has exactly the fixed endpoint difference. -/
theorem FibreNCPathModel.homotopy_d {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) :
    CochainComplex.HomComplex.δ (-1) 0 C.homotopy =
      CochainComplex.HomComplex.Cochain.ofHom C.secondEndpoint -
        CochainComplex.HomComplex.Cochain.ofHom C.firstEndpoint :=
  relativeHomotopy_d C.projection C.fibration C.firstEndpoint C.secondEndpoint
    C.first_section C.second_section

/-- The actual path comparison after the native universal derived-fibre map. -/
def comparisonPath {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) (ω : ClosedForm GF n)
    (L : LinearPath C.firstEndpoint C.secondEndpoint C.homotopy C.homotopy_d ω) :=
  L.edge.map ((realize k).map C.fibre)

/-- The first endpoint is the actual pulled source form, with its fibre square fixed. -/
theorem comparisonPath_source {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) (ω : ClosedForm GF n) :
    ((realize k).map C.fibre).app (op ⦋0⦌)
      (((realize k).map C.firstEndpoint).app (op ⦋0⦌) ω) =
    (closedPullback (DerivedStackFibreModels.first Z) GX GZ n).app (op ⦋0⦌)
      ((closedPullback f GF GX n).app (op ⦋0⦌) ω) := by
  exact congrArg (fun t => t.app (op ⦋0⦌) ω) C.first_realization_square

/-- The second endpoint is the other actual pulled source form. -/
theorem comparisonPath_target {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) (ω : ClosedForm GF n) :
    ((realize k).map C.fibre).app (op ⦋0⦌)
      (((realize k).map C.secondEndpoint).app (op ⦋0⦌) ω) =
    (closedPullback (DerivedStackFibreModels.second Z) GY GZ n).app (op ⦋0⦌)
      ((closedPullback g GF GY n).app (op ⦋0⦌) ω) := by
  exact congrArg (fun t => t.app (op ⦋0⦌) ω) C.second_realization_square

/-- Actual source isotropic paths and the fixed universal comparison construct the residue loop. -/
def derivedResiduePaths {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) (ω : ClosedForm GF n)
    (L : LinearPath C.firstEndpoint C.secondEndpoint C.homotopy C.homotopy_d ω)
    (h : IsotropicPath GX n ((closedPullback f GF GX n).app (op ⦋0⦌) ω))
    (j : IsotropicPath GY n ((closedPullback g GF GY n).app (op ⦋0⦌) ω)) : ResiduePaths GZ n where
  left := (closedPullback (DerivedStackFibreModels.first Z) GX GZ n).app (op ⦋0⦌)
    ((closedPullback f GF GX n).app (op ⦋0⦌) ω)
  right := (closedPullback (DerivedStackFibreModels.second Z) GY GZ n).app (op ⦋0⦌)
    ((closedPullback g GF GY n).app (op ⦋0⦌) ω)
  first := (h.map (closedPullback (DerivedStackFibreModels.first Z) GX GZ n)).ofEq
    (closedPullback_zero _ _ _ _) rfl
  second := (j.map (closedPullback (DerivedStackFibreModels.second Z) GY GZ n)).ofEq
    (closedPullback_zero _ _ _ _) rfl
  comparison := (comparisonPath C ω L).ofEq (comparisonPath_source C ω) (comparisonPath_target C ω)

/-- The residue is the native normalized homology class of h + u(ω) - j - s₀(f*ω). -/
def derivedResidueClass {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} {Z : FibreStackModel P f g}
    {GF : GlobalNCModel D 2 NC F.functor} {GX : GlobalNCModel D 2 NC X.functor}
    {GY : GlobalNCModel D 2 NC Y.functor} {GP : GlobalNCModel D 2 NC P.P}
    {GZ : GlobalNCModel D 2 NC Z.stack.functor} {n : ℤ}
    (C : FibreNCPathModel Z GF GX GY GP GZ n) (ω : ClosedForm GF n)
    (L : LinearPath C.firstEndpoint C.secondEndpoint C.homotopy C.homotopy_d ω)
    (h : IsotropicPath GX n ((closedPullback f GF GX n).app (op ⦋0⦌) ω))
    (j : IsotropicPath GY n ((closedPullback g GF GY n).app (op ⦋0⦌) ω)) :
    (ncComplex GZ).homology (n - 3) :=
  residueClass (derivedResiduePaths C ω L h j)

/-- A source assembly chooses one compatible NC diagram for the entire fibre diagram.
Arbitrary independent injective replacements are not asserted to satisfy strict path squares. -/
structure FibreNCModels {X Y F : DerivedStack Q} {P : NaturalPathModel F}
    {f : StackMap X F} {g : StackMap Y F} (Z : FibreStackModel P f g) (n : ℤ) where
  target : GlobalNCModel D 2 NC F.functor
  first : GlobalNCModel D 2 NC X.functor
  second : GlobalNCModel D 2 NC Y.functor
  path : GlobalNCModel D 2 NC P.P
  intersection : GlobalNCModel D 2 NC Z.stack.functor
  comparison : FibreNCPathModel Z target first second path intersection n

end MathlibExt.AlgebraicGeometry.DerivedFibreClosingPaths
