/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasimapConstantDefectFamilies
public import MathlibExt.AlgebraicGeometry.QuasimapUniversalFamilies
public import Batteries.Util.ProofWanted

/-!
# Native quasimap family and regularization construction requests

Each request uses the actual torsor, section, unstable ideal, local
quotient length, equivariant Picard generator, and native GIT Proj.
The regular quotient is the canonical invariant-evaluation map.
The rational length construction retains finite generation of the
actual homogeneous invariant algebra through StableGITTarget.

Individual regularization and the L_theta degree-defect formula are
separate requests. Family regularization is restricted to the paper's
smooth, irreducible, constant-length, section-presented situation; its
result keeps a nonempty shrinking, common source modification and
normalized basepoint relabelling.

References: Ciocan-Fontanine–Kim–Maulik, arXiv:1106.3724v2,
Definitions 2.4.1, 3.1.6, 7.1.1, Lemma 7.1.2 and the proof of
Theorem 7.1.6, pp. 44–45. Generic source integrations remain those of
the native torsor, line-descent and marked-curve contracts.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.QuasimapNativeSourcesWanted

open MathlibExt.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open GroupTorsorGeometry QuasimapAssociatedFamilies
open QuasimapBasepointDefects QuasimapSectionLengths QuasimapPicardDegrees
open QuasimapInvariantAlgebras QuasimapRegularizationModels QuasimapConstantDefectFamilies
open QuasimapUniversalFamilies

def_wanted nativeCharacterInvariantAlgebra
    {R : Type} [CommRing R] (G W : Over (Spec (.of R))) [GrpObj G] [ModObj G W]
    (L : CharacterPolarization G W) : InvariantAlgebraModel G W L

variable {G W : Over (Spec (.of ℂ))} [GrpObj G] [ModObj G W]
    [IsAffine G.left] [IsAffine W.left]
    {L : CharacterPolarization G W} [InvariantAlgebraModel G W L]
    {n g : ℕ}

def_wanted nativeIndividualDegrees
    (F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ))))) :
    Σ D : InducedDegrees G W F.quotient, DegreeFunctional D

/-- The unstable locus descends along the associated-bundle quotient: the
`G`-invariant closed subscheme `P × W^us` of `P × W` is the pullback of a closed
subscheme of the associated bundle (fppf descent of closed subschemes). -/
def_wanted nativeAssociatedUnstable {T : Over (Spec (.of ℂ))}
    (P : QuotientObject G W T) (B : AssociatedBundle G W P) : AssociatedUnstable L P B

/-- Off its base locus a quasimap lands in the stable locus, so its torsor and
equivariant map descend to an actual map to the stable quotient
(Ciocan-Fontanine–Kim–Maulik, before Lemma 7.1.2). -/
def_wanted nativeOffBaseMap {T : Over (Spec (.of ℂ))} (F : Family G W n g T)
    (B : AssociatedFamily F) (U : AssociatedUnstable L F.quotient B)
    (Q : StableGITTarget G W L) : OffBaseMap F B U Q

def_wanted nativeIndividualRegularization
    (F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ)))))
    (B : AssociatedFamily F) (U : AssociatedUnstable L F.quotient B)
    (h : IsPrestable F B U) (Q : StableGITTarget G W L) (O : OffBaseMap F B U Q) :
    RegularizedMap F B U Q O

def_wanted nativeBasepointLength
    (F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ)))))
    (B : AssociatedFamily F) (U : AssociatedUnstable L F.quotient B)
    (h : IsPrestable F B U) (Q : StableGITTarget G W L) (x : F.curve.X) :
    BasepointLength G W F.quotient L x

theorem_wanted nativeThetaDegreeDefect
    (F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ)))))
    (B : AssociatedFamily F) (U : AssociatedUnstable L F.quotient B)
    (h : IsPrestable F B U) (Q : StableGITTarget G W L) (O : OffBaseMap F B U Q)
    (R : RegularizedMap F B U Q O) (D : IndividualDegrees R)
    (lengths : ∀ x : F.curve.X, BasepointLength G W F.quotient L x) :
    (thetaDegreeDefect D : ℚ) = totalBasepointLength F B U h lengths

theorem_wanted nativeGeneratedIdealLength
    (F : Family G W n g (Over.mk (𝟙 (Spec (.of ℂ)))))
    (B : AssociatedFamily F) (U : AssociatedUnstable L F.quotient B)
    (h : IsPrestable F B U) (Q : StableGITTarget G W L)
    (generated : DegreeOneGeneration G W L) (x : F.curve.X)
    (D : BasepointLength G W F.quotient L x) :
    ∃ a : ℕ, basepointIdealLength L U x = (a : ℕ∞) ∧ D.value = a

def_wanted nativeQuasimapFamilyStack
    (G W : Over (Spec (.of ℂ))) [GrpObj G] [ModObj G W]
    [IsAffine G.left] [IsAffine W.left] [Flat G.hom] [LocallyOfFinitePresentation G.hom]
    (n g : ℕ) : {M : FamilyStack G W n g // FamilyCoherence M}

def_wanted nativeUniversalAssociatedFamily
    (G W : Over (Spec (.of ℂ))) [GrpObj G] [ModObj G W]
    [IsAffine G.left] [IsAffine W.left] (n g : ℕ)
    (M : FamilyStack G W n g) (C : FamilyCoherence M) : UniversalAssociatedFamily M

def_wanted nativeQuasimapFamilyReindex
    [Flat G.hom] [LocallyOfFinitePresentation G.hom]
    {T V : Over (Spec (.of ℂ))} (f : V ⟶ T) : FamilyReindex G W n g f

def_wanted nativeQuasimapFamilyShrinking
    {T : Over (Spec (.of ℂ))} (F : Family G W n g T) (B : AssociatedFamily F)
    (U : AssociatedUnstable L F.quotient B) (V : T.left.Opens) (h : Nonempty V) :
    {D : FamilyShrinking F B U // D.parameter = V}

def_wanted nativeConstantDefectFamilyRegularization
    {T : Over (Spec (.of ℂ))} (F : Family G W n g T) (B : AssociatedFamily F)
    (U : AssociatedUnstable L F.quotient B) (K : ConstantDefectPresentation F B U)
    (Q : StableGITTarget G W L) :
    Σ R : CommonCurveRegularization F B U Q, CommonNormalization F B U K R

end WantedExt.AlgebraicGeometry.QuasimapNativeSourcesWanted
