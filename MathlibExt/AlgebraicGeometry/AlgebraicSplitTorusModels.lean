/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicWeightBundleModels
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Topology.Connected.Clopen

/-!
# Actual split tori, characters, cocharacters and chambers

The split torus is Spec C[Z^r] with its native Hopf group structure.
Character coordinates are fixed by the original Laurent-coordinate
pullback. A splitting is an actual group-scheme isomorphism, and a
chamber is the connected component of the complement of the actual
normal-character hyperplanes.

Reference: Maulik--Okounkov 1211.1287v3, Sections3.1--3.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AlgebraicSplitTorusModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels

abbrev Lattice (r : ℕ) := Fin r → ℤ
abbrev CoordinateRing (r : ℕ) := AddMonoidAlgebra ℂ (Lattice r)

/-- The group object is the native Hopf-induced group on this actual affine scheme. -/
abbrev splitTorus (r : ℕ) : Over base := (Spec (.of (CoordinateRing r))).asOver base

instance splitTorusGroup (r : ℕ) : GrpObj (splitTorus r) :=
  inferInstanceAs (GrpObj ((Spec (.of (CoordinateRing r))).asOver base))

/-- The original character monomial is a unit over every coefficient algebra. -/
def characterUnit (r : ℕ) (a : Lattice r) : (CoordinateRing r)ˣ :=
  ⟨AddMonoidAlgebra.single a 1, AddMonoidAlgebra.single (-a) 1,
    by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def],
    by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]⟩

/-- An actual complex point evaluates every monomial by its coordinate units. -/
def characterEvaluation {r : ℕ} (g : Fin r → ℂˣ) : Multiplicative (Lattice r) →* ℂˣ where
  toFun a := ∏ i, g i ^ a.toAdd i
  map_one' := by simp
  map_mul' a b := by simp [zpow_add, Finset.prod_mul_distrib]

def pointEvaluation {r : ℕ} (g : Fin r → ℂˣ) : CoordinateRing r →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Lattice r) ((Units.coeHom ℂ).comp (characterEvaluation g))

def splitPoint {r : ℕ} (g : Fin r → ℂˣ) : 𝟙_ (Over base) ⟶ splitTorus r :=
  Over.homMk (Spec.map (CommRingCat.ofHom (pointEvaluation g).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : (pointEvaluation g).toRingHom.comp (algebraMap ℂ (CoordinateRing r)) = RingHom.id ℂ :=
      by
      ext c
      exact (pointEvaluation g).commutes c
    simpa only [h, CommRingCat.ofHom_id] using Spec.map_id (.of ℂ))

/-- A torus model has an actual group-scheme coordinate isomorphism. -/
structure TorusModel (T : Over base) [GrpObj T] where
  rank : ℕ
  iso : T ≅ splitTorus rank
  [hom : IsMonHom iso.hom]
  [inv : IsMonHom iso.inv]

attribute [instance] TorusModel.hom TorusModel.inv

def TorusModel.point {T : Over base} [GrpObj T] (M : TorusModel T)
    (g : Fin M.rank → ℂˣ) : 𝟙_ (Over base) ⟶ T := splitPoint g ≫ M.iso.inv

/-- Character exponents are pinned by the original actual scheme ring map. -/
structure CharacterCoordinates {T : Over base} [GrpObj T] (M : TorusModel T) (χ : Character T) where
  exponent : Lattice M.rank
  normalized : χ.map.left.appTop (gmUnit : Γ(Gm.left, ⊤)) =
    M.iso.hom.left.appTop
      ((Scheme.ΓSpecIso (.of (CoordinateRing M.rank))).inv.hom
        (characterUnit M.rank exponent : CoordinateRing M.rank))

/-- The subtorus inclusion is an actual closed group-scheme morphism. -/
structure Subtorus (A T : Over base) [GrpObj A] [GrpObj T] where
  inclusion : A ⟶ T
  [hom : IsMonHom inclusion]
  [closed : IsClosedImmersion inclusion.left]

attribute [instance] Subtorus.hom Subtorus.closed

/-- A complement realizes T/A and fixes the inclusion on every scheme test. -/
structure TorusSplitting {A T : Over base} [GrpObj A] [GrpObj T] (S : Subtorus A T) where
  quotient : Over base
  [group : GrpObj quotient]
  model : TorusModel quotient
  iso : T ≅ A ⊗ quotient
  [hom : IsMonHom iso.hom]
  [inv : IsMonHom iso.inv]
  inclusion : S.inclusion ≫ iso.hom = lift (𝟙 A) (toUnit A ≫ η[quotient])

attribute [instance] TorusSplitting.group TorusSplitting.hom TorusSplitting.inv

def TorusSplitting.projection {A T : Over base} [GrpObj A] [GrpObj T]
    {S : Subtorus A T} (P : TorusSplitting S) : T ⟶ P.quotient := P.iso.hom ≫ snd A P.quotient

def restrictedCharacter {A T : Over base} [GrpObj A] [GrpObj T]
    (S : Subtorus A T) (χ : Character T) : Character A :=
  { map := S.inclusion ≫ χ.map, hom := inferInstance }

def pairedCharacter {A : Over base} [GrpObj A] (χ : Character A)
    (lambda : Gm ⟶ A) [IsMonHom lambda] : Character Gm :=
  { map := lambda ≫ χ.map, hom := inferInstance }

/-- Pairing uses the integer classification of that actual composite character. -/
def pairing {A : Over base} [GrpObj A] (χ : Character A) (lambda : Gm ⟶ A)
    [IsMonHom lambda] (p : IntegerCharacter (pairedCharacter χ lambda)) : ℤ := p.weight

def realPairing {r : ℕ} (a : Lattice r) (v : Fin r → ℝ) : ℝ := ∑ i, (a i : ℝ) * v i

/-- These exponents are coordinates of the actual normal characters. -/
structure RootCoordinates {A : Over base} [GrpObj A] (M : TorusModel A) where
  count : ℕ
  character : Fin count → Character A
  coordinates : ∀ j, CharacterCoordinates M (character j)
  nonzero : ∀ j, (coordinates j).exponent ≠ 0

def regularCocharacters {A : Over base} [GrpObj A] {M : TorusModel A}
    (R : RootCoordinates M) : Set (Fin M.rank → ℝ) :=
  {v | ∀ j, realPairing (R.coordinates j).exponent v ≠ 0}

/-- A chamber is computed as an actual connected component of the hyperplane complement. -/
structure Chamber {A : Over base} [GrpObj A] {M : TorusModel A} (R : RootCoordinates M) where
  reference : Fin M.rank → ℝ
  regular : reference ∈ regularCocharacters R

def Chamber.region {A : Over base} [GrpObj A] {M : TorusModel A}
    {R : RootCoordinates M} (C : Chamber R) : Set (Fin M.rank → ℝ) :=
  connectedComponentIn (regularCocharacters R) C.reference

end MathlibExt.AlgebraicGeometry.AlgebraicSplitTorusModels
