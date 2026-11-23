/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetWeakComponentCoefficients
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetRelativeBaseComparison

/-!
# Actual relative local-coefficient maps of an original square

The target system determines all four original pullbacks. The commuting
base square gives the source congruence/composition transport; both actual
coefficient triangles then force the whole cokernel map. Weak actual mates
give its quasi-isomorphism by the stock monomorphic-arrow theorem.

A natural target-system Iso also gives the actual relative-chain Iso with
its original quotient square. No flatness, coefficient calibration square,
relative-QI witness or transported desired map is input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe uR u

namespace SSet

section SystemIso

variable {R : Type uR} [CommRing R] {X Y : SSet.{u}}

/-- The relative-chain Iso induced by an actual target-system Iso. -/
public def localCoefficientRelativeSystemIso
    (i : X ⟶ Y) {L M : SSet.LocalSystem R Y} (E : L ≅ M) :
    cokernel (localCoefficientPullbackChainMap i L) ≅
      cokernel (localCoefficientPullbackChainMap i M) := by
  let a : localCoefficientChainComplex (L.pullback i) ⟶ localCoefficientChainComplex L :=
    localCoefficientPullbackChainMap i L
  let b : localCoefficientChainComplex (M.pullback i) ⟶ localCoefficientChainComplex M :=
    localCoefficientPullbackChainMap i M
  let EX := Functor.isoWhiskerLeft (SSet.mapFundamentalGroupoid i) E
  let eX : localCoefficientChainComplex (L.pullback i) ≅
      localCoefficientChainComplex (M.pullback i) :=
    (localCoefficientChainComplexFunctor (R := R) (X := X)).mapIso EX
  let eY : localCoefficientChainComplex L ≅ localCoefficientChainComplex M :=
    (localCoefficientChainComplexFunctor (R := R) (X := Y)).mapIso E
  have hs : a ≫ eY.hom = eX.hom ≫ b :=
    (localCoefficientPullbackChainMap_naturality i E.hom).symm
  exact cokernel.mapIso a b eX eY hs

@[reassoc]
public theorem localCoefficientRelativeSystemIso_π
    (i : X ⟶ Y) {L M : SSet.LocalSystem R Y} (E : L ≅ M) :
    cokernel.π (localCoefficientPullbackChainMap i L) ≫
        (localCoefficientRelativeSystemIso i E).hom =
      localCoefficientChainMap E.hom ≫ cokernel.π (localCoefficientPullbackChainMap i M) := by
  unfold localCoefficientRelativeSystemIso
  exact cokernel.π_desc (localCoefficientPullbackChainMap i L) _ _

end SystemIso

section OriginalSquare

variable {X B H W : SSet.{u}}

/-- The actual source relative arrow of the original base square. Its
source uses the original composite f≫j, aligned to i≫a by the square. -/
public def localCoefficientRelativeSquareSourceArrow
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ W) :
    localCoefficientChainComplex (L.pullback (f ≫ j)) ⟶
      localCoefficientChainComplex (L.pullback a) :=
  localCoefficientChainMapOver i a (f ≫ j) sq.w.symm L

public theorem localCoefficientRelativeSquareSourceArrow_eq
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ W) :
    localCoefficientRelativeSquareSourceArrow i f a j sq L =
      localCoefficientChainMapOver i a (f ≫ j) sq.w.symm L := by
  unfold localCoefficientRelativeSquareSourceArrow
  rfl

private theorem relativeSquareCoefficientSquare
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ W) :
    localCoefficientRelativeSquareSourceArrow i f a j sq L ≫
        localCoefficientPullbackChainMap a L =
      localCoefficientChainMapOver f j (f ≫ j) rfl L ≫
        localCoefficientPullbackChainMap j L :=
  (localCoefficientChainMapOver_comp i a (f ≫ j) sq.w.symm L).trans
    (localCoefficientChainMapOver_comp f j (f ≫ j) rfl L).symm

/-- The ACTUAL original coefficient-relative map of the original square.
It has the literal original cokernel projections and original base maps. -/
public def localCoefficientRelativeSquareMap
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ W) :
    cokernel (localCoefficientRelativeSquareSourceArrow i f a j sq L) ⟶
      cokernel (localCoefficientPullbackChainMap j L) :=
  cokernel.map _ _ (localCoefficientChainMapOver f j (f ≫ j) rfl L)
    (localCoefficientPullbackChainMap a L) (relativeSquareCoefficientSquare i f a j sq L)

@[reassoc]
public theorem localCoefficientRelativeSquareMap_π
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ W) :
    cokernel.π (localCoefficientRelativeSquareSourceArrow i f a j sq L) ≫
        localCoefficientRelativeSquareMap i f a j sq L =
      localCoefficientPullbackChainMap a L ≫ cokernel.π (localCoefficientPullbackChainMap j L) := by
  unfold localCoefficientRelativeSquareMap
  exact cokernel.π_desc _ _ _

/-- Weak ACTUAL mates give a relative quasi-isomorphism, with both
horizontal monos derived from the original inclusions. The final collar
application derives these two weak maps from its actual homotopies. -/
public theorem localCoefficientRelativeSquareMap_quasiIso_of_weak_mates
    (i : X ⟶ B) [Mono i] (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W) [Mono j]
    (sq : CommSq i f a j) (hf : realizationWeakEquivalences f)
    (ha : realizationWeakEquivalences a) (L : SSet.LocalSystem ℤ W) :
    QuasiIso (localCoefficientRelativeSquareMap i f a j sq L) := by
  let m := localCoefficientRelativeSquareSourceArrow i f a j sq L
  let n := localCoefficientPullbackChainMap j L
  let s := localCoefficientChainMapOver f j (f ≫ j) rfl L
  let t := localCoefficientPullbackChainMap a L
  let : Mono m := localCoefficientChainMapOver_mono i a (f ≫ j) sq.w.symm L
  let : Mono n := localCoefficientPullbackChainMap_mono_of_mono j L
  let P := MorphismProperty.monomorphisms (ChainComplex (ModuleCat.{u} ℤ) ℕ)
  let A : P.Arrow ⊤ ⊤ := MorphismProperty.Arrow.mk m (inferInstance : Mono m)
  let B' : P.Arrow ⊤ ⊤ := MorphismProperty.Arrow.mk n (inferInstance : Mono n)
  have hs : m ≫ t = s ≫ n := relativeSquareCoefficientSquare i f a j sq L
  let φ : A ⟶ B' := MorphismProperty.Arrow.homMk s t hs.symm
  have hLeft : QuasiIso φ.left :=
    localCoefficientChainMapOver_quasiIso_of_weak_allComponents f hf j (f ≫ j) rfl L
  have hRight : QuasiIso φ.right :=
    realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap_allComponents a ha L
  have h := HomologicalComplex.HomologySequence.quasiIso_coker_map φ hLeft hRight
  change QuasiIso (cokernel.map m n s t hs) at h
  exact h

end OriginalSquare

end SSet

end
