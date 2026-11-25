/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual nilpotent presentations of p-adic formal schemes

The affine formal spectrum is the actual diagram
`n ↦ Spec(A/(I + (p)^(n+1)))`. A p-adic formal scheme over this base is a
diagram of schemes with a Cartesian structure map to those thickenings.
Thus each earlier level is exactly reduction of every later level.
Morphisms are actual natural transformations over the base diagram.

This is the nilpotent-thickening presentation of adic formal schemes,
EGA I, §10.1; Bhatt--Scholze, arXiv:1905.08229v4, Definition 4.1.
It retains non-Noetherian and nonreduced bases. The existing completed
locally ringed Spf realization is source integration:
TauCetiProject/TauCeti, revision
`62bbc0596dc3539d488232e4e924a338548ea0a9`,
`TauCeti/AlgebraicGeometry/FormalScheme/Spf/Basic.lean` (Apache 2.0),
and AxiomMath/Stacks, revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/AlgebraicGeometry/FormalScheme/FormalSpectrum.lean`
(Apache 2.0). No arbitrary formal carrier or global sections is supplied.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PadicFormalSchemes

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (A : Type u) [CommRing A] (I : Ideal A)

/-- The actual nth ideal of the formal p-adic completion of `A/I`. -/
def levelIdeal (n : ℕ) : Ideal A :=
  I ⊔ (Ideal.span {(p : A)}) ^ (n + 1)

/-- Higher powers define smaller actual quotient ideals. -/
theorem levelIdeal_antitone : Antitone (levelIdeal p A I) := by
  intro n m h
  exact sup_le_sup le_rfl
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The actual nth affine thickening ring. -/
abbrev LevelRing (n : ℕ) := A ⧸ levelIdeal p A I n

/-- Reduction of the actual later thickening to the earlier one. -/
def reduction {n m : ℕ} (h : n ≤ m) :
    LevelRing p A I m →+* LevelRing p A I n :=
  Ideal.Quotient.factor (levelIdeal_antitone p A I h)

@[simp] theorem reduction_mk {n m : ℕ} (h : n ≤ m) (a : A) :
    reduction p A I h (Ideal.Quotient.mk (levelIdeal p A I m) a) =
      Ideal.Quotient.mk (levelIdeal p A I n) a := rfl

@[simp] theorem reduction_refl (n : ℕ) :
    reduction p A I (le_refl n) = RingHom.id _ := by
  exact Ideal.Quotient.factor_eq

theorem reduction_comp {n m k : ℕ} (h : n ≤ m) (j : m ≤ k) :
    (reduction p A I h).comp (reduction p A I j) =
      reduction p A I (h.trans j) := by
  exact Ideal.Quotient.factor_comp _ _

/-- The actual increasing system of nilpotent affine thickenings. -/
def spfDiagram : ℕ ⥤ Scheme.{u} where
  obj n := Spec (CommRingCat.of (LevelRing p A I n))
  map {n m} h := Spec.map
    (CommRingCat.ofHom (reduction p A I (leOfHom h)))
  map_id n := by
    change Spec.map (CommRingCat.ofHom
      (reduction p A I (le_refl n))) = _
    rw [reduction_refl]
    exact Spec.map_id _
  map_comp {n m k} h j := by
    change Spec.map (CommRingCat.ofHom
      (reduction p A I ((leOfHom h).trans (leOfHom j)))) = _
    rw [← reduction_comp p A I (leOfHom h) (leOfHom j)]
    exact Spec.map_comp
      (CommRingCat.ofHom (reduction p A I (leOfHom j)))
      (CommRingCat.ofHom (reduction p A I (leOfHom h)))

variable {A I}

/-- A ring map preserving the ideals preserves every actual level ideal. -/
theorem map_levelIdeal_le {B : Type u} [CommRing B] {J : Ideal B}
    (f : A →+* B) (h : I.map f ≤ J) (n : ℕ) :
    (levelIdeal p A I n).map f ≤ levelIdeal p B J n := by
  have hp : (Ideal.span {(p : A)}).map f =
      Ideal.span {(p : B)} := by
    rw [Ideal.map_span]
    simp
  rw [levelIdeal, Ideal.map_sup, Ideal.map_pow, hp]
  exact sup_le_sup h le_rfl

/-- The fixed ring map on every nilpotent thickening. -/
def levelMap {B : Type u} [CommRing B] {J : Ideal B}
    (f : A →+* B) (h : I.map f ≤ J) (n : ℕ) :
    LevelRing p A I n →+* LevelRing p B J n :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (levelIdeal p B J n)).comp f) (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (map_levelIdeal_le p f h n (Ideal.mem_map_of_mem f ha)))

@[simp] theorem levelMap_mk {B : Type u} [CommRing B] {J : Ideal B}
    (f : A →+* B) (h : I.map f ≤ J) (n : ℕ) (a : A) :
    levelMap p f h n (Ideal.Quotient.mk (levelIdeal p A I n) a) =
      Ideal.Quotient.mk (levelIdeal p B J n) (f a) := rfl

/-- The actual formal-spectrum map induced by the actual ring map. -/
def mapDiagram {B : Type u} [CommRing B] {J : Ideal B}
    (f : A →+* B) (h : I.map f ≤ J) :
    spfDiagram p B J ⟶ spfDiagram p A I where
  app n := Spec.map (CommRingCat.ofHom (levelMap p f h n))
  naturality {n m} j := by
    dsimp only [spfDiagram]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    rfl

/-- Formal-spectrum maps compose by the fixed underlying ring maps. -/
theorem mapDiagram_comp {B C : Type u} [CommRing B] [CommRing C]
    {J : Ideal B} {K : Ideal C}
    (f : A →+* B) (g : B →+* C) (hf : I.map f ≤ J)
    (hg : J.map g ≤ K) :
    mapDiagram p g hg ≫ mapDiagram p f hf =
      mapDiagram p (g.comp f) (by
        rw [← Ideal.map_map]
        exact (Ideal.map_mono hf).trans hg) := by
  ext n
  change Spec.map (CommRingCat.ofHom (levelMap p g hg n)) ≫
    Spec.map (CommRingCat.ofHom (levelMap p f hf n)) =
      Spec.map (CommRingCat.ofHom (levelMap p (g.comp f) _ n))
  rw [← Spec.map_comp]
  congr 1
  ext a
  rfl

/-- The identity ring map gives the identity formal-spectrum map. -/
@[simp] theorem mapDiagram_id :
    mapDiagram p (RingHom.id A) (I := I) (J := I) (by simp) =
      𝟙 (spfDiagram p A I) := by
  ext n
  have h : levelMap p (RingHom.id A) (I := I) (J := I)
      (by simp) n = RingHom.id _ := by ext a; rfl
  dsimp only [mapDiagram, NatTrans.id_app]
  rw [h]
  exact Spec.map_id _

variable (A I)

/-- Cartesian reduction to the actual formal base at every level. -/
def IsFormal (X : Over (spfDiagram p A I)) : Prop :=
  ∀ {n m : ℕ} (h : n ⟶ m),
    IsPullback (X.left.map h) (X.hom.app n) (X.hom.app m)
      ((spfDiagram p A I).map h)

/-- p-adic formal schemes in their actual nilpotent presentation. -/
abbrev FormalScheme :=
  ObjectProperty.FullSubcategory (IsFormal p A I)

/-- The actual underlying diagram of schemes. -/
abbrev FormalScheme.diagram (X : FormalScheme.{u} p A I) :=
  X.obj.left

/-- The actual structure map to the formal base. -/
abbrev FormalScheme.structureMap (X : FormalScheme.{u} p A I) :=
  X.obj.hom

/-- The base formal spectrum, with its literal quotient diagram. -/
def Spf : FormalScheme.{u} p A I :=
  ⟨Over.mk (𝟙 (spfDiagram p A I)), fun {_ _} h ↦ by
    exact IsPullback.of_id_snd (f := (spfDiagram p A I).map h)⟩

/-- The actual residue-base map to each formal level. -/
def residueToLevel (n : ℕ) : (A ⧸ I) →+* LevelRing p A I n :=
  Ideal.Quotient.factor (show I ≤ levelIdeal p A I n from le_sup_left)

/-- Forget only the nilpotent base to regard every level over Spec(A/I). -/
def baseToResidue : spfDiagram p A I ⟶
    (Functor.const ℕ).obj (Spec (CommRingCat.of (A ⧸ I))) where
  app n := Spec.map (CommRingCat.ofHom (residueToLevel p A I n))
  naturality {n m} h := by
    change Spec.map (CommRingCat.ofHom (reduction p A I (leOfHom h))) ≫
      Spec.map (CommRingCat.ofHom (residueToLevel p A I m)) = _
    rw [← Spec.map_comp]
    congr 1
    ext a
    rfl

/-- The actual ordinary residue-base schemes in the formal diagram. -/
def FormalScheme.algebraicDiagram (X : FormalScheme.{u} p A I) :
    ℕ ⥤ Over (Spec (CommRingCat.of (A ⧸ I))) where
  obj n := Over.mk (X.structureMap.app n ≫ (baseToResidue p A I).app n)
  map {n m} h := Over.homMk (X.diagram.map h) (by
    change X.diagram.map h ≫
      (X.structureMap.app m ≫ (baseToResidue p A I).app m) =
        X.structureMap.app n ≫ (baseToResidue p A I).app n
    rw [← Category.assoc, X.structureMap.naturality h, Category.assoc,
      (baseToResidue p A I).naturality h]
    simp)
  map_id _ := by ext1; exact X.diagram.map_id _
  map_comp _ _ := by ext1; exact X.diagram.map_comp _ _

variable {p A I}

/-- Each morphism is its actual natural transformation of thickenings. -/
abbrev FormalScheme.Hom.diagram {X Y : FormalScheme.{u} p A I}
    (f : X ⟶ Y) : X.diagram ⟶ Y.diagram :=
  f.hom.left

/-- The actual base equation, retained on every component. -/
theorem FormalScheme.Hom.base {X Y : FormalScheme.{u} p A I}
    (f : X ⟶ Y) : FormalScheme.Hom.diagram f ≫
      Y.structureMap = X.structureMap :=
  f.hom.w

end MathlibExt.AlgebraicGeometry.PadicFormalSchemes
