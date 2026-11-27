/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), `AlgebraicGeometry.hasSheafify_moduleCat`:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: use the general bounded-prism formal slice, an arbitrary coefficient ring and the
semilinear Frobenius.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import MathlibExt.AlgebraicGeometry.PadicFormalSchemes
public import MathlibExt.RingTheory.BoundedPrisms

/-!
# The relative bounded-prism site of an actual p-adic formal scheme

Objects are actual bounded prisms over `(A,I)` and compatible maps
`Spec(B/(J+(p)^(n+1))) → X_n` over the actual base thickenings.
The maps and all base equations are actual natural transformations.

Covers use the complete-flat derived criterion: higher actual Tor with
`A/(p,I)` vanishes and the degree-zero quotient is faithfully flat.
The structure presheaf is the actual ring `B` as an `A`-module. Its
Frobenius is semilinear over the actual delta Frobenius of `A`.

Reference: Bhatt--Scholze, arXiv:1905.08229v4, Definitions 3.2 and 4.1,
Lemma 3.5 and Remark 4.3. This is not restricted to `(Z_p,(p))` or to
ordinary prime-field schemes.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativePrismaticSite

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.AlgebraicGeometry.PadicFormalSchemes

universe u

variable (p : ℕ) [Fact p.Prime] (P : Prism.{u} p)
  (X : FormalScheme p P.ring P.ideal)

/-- Actual relative prisms and formal maps over the fixed base prism. -/
structure Obj where
  prism : Prism.{u} p
  base : P ⟶ prism
  point : spfDiagram p prism.ring prism.ideal ⟶ X.diagram
  point_base : point ≫ X.structureMap =
    mapDiagram p base.hom base.ideal

/-- A morphism is a delta map in the geometric opposite direction. -/
structure Hom (U V : Obj p P X) where
  map : V.prism ⟶ U.prism
  base : V.base ≫ map = U.base
  point : mapDiagram p map.hom map.ideal ≫ V.point = U.point

@[ext] theorem Hom.ext {U V : Obj p P X} (f g : Hom p P X U V)
    (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity of a site object. -/
def Hom.id (U : Obj p P X) : Hom p P X U U where
  map := 𝟙 U.prism
  base := Category.comp_id _
  point := by
    change mapDiagram p (RingHom.id U.prism.ring)
      (I := U.prism.ideal) (J := U.prism.ideal) (by simp) ≫
        U.point = U.point
    rw [mapDiagram_id]
    exact Category.id_comp _

/-- Composition respects the actual formal point/base equations. -/
def Hom.comp {U V W : Obj p P X}
    (f : Hom p P X U V) (g : Hom p P X V W) : Hom p P X U W where
  map := g.map ≫ f.map
  base := by rw [← Category.assoc, g.base, f.base]
  point := by
    change mapDiagram p (f.map.hom.comp g.map.hom) _ ≫ W.point = _
    rw [← mapDiagram_comp p g.map.hom f.map.hom
      g.map.ideal f.map.ideal, Category.assoc, g.point, f.point]

instance : Category (Obj p P X) where
  Hom := Hom p P X
  id := Hom.id p P X
  comp := Hom.comp p P X
  id_comp _ := by apply Hom.ext; exact Category.comp_id _
  comp_id _ := by apply Hom.ext; exact Category.id_comp _
  assoc _ _ _ := by apply Hom.ext; exact (Category.assoc _ _ _).symm

/-- The structural algebra is the actual base-prism map. -/
instance Obj.baseAlgebra (U : Obj p P X) :
    Algebra P.ring U.prism.ring := U.base.hom.toAlgebra

/-- The real ring map of a site morphism is linear on structural scalars. -/
def Hom.linear {U V : Obj p P X} (f : U ⟶ V) :
    V.prism.ring →ₗ[P.ring] U.prism.ring where
  toFun := f.map.hom
  map_add' := map_add _
  map_smul' a b := by
    change f.map.hom (V.base.hom a * b) =
      U.base.hom a * f.map.hom b
    rw [map_mul]
    have h := congrArg (fun t : P ⟶ U.prism ↦ t.hom a) f.base
    exact congrArg (· * f.map.hom b) h

/-- Complete faithful flatness, using the actual derived Tor criterion. -/
def IsCover {U V : Obj p P X} (f : U ⟶ V) : Prop :=
  let A := V.prism.ring
  let B := U.prism.ring
  let J := completionIdeal p V.prism.ideal
  letI := f.map.hom.toAlgebra
  (∀ n : ℕ, IsZero
    (((Tor (ModuleCat.{u} A) (n + 1)).obj (ModuleCat.of A B)).obj
      (ModuleCat.of A (A ⧸ J)))) ∧
  letI := (Ideal.Quotient.lift J
    ((Ideal.Quotient.mk (J.map f.map.hom)).comp f.map.hom)
    (fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem f.map.hom ha))).toAlgebra
  Module.FaithfullyFlat (A ⧸ J) (B ⧸ J.map f.map.hom)

/-- The topology generated by the actual completely flat covers. -/
def topology : GrothendieckTopology (Obj p P X) :=
  sInf {J | ∀ (U V : Obj p P X) (f : U ⟶ V), IsCover p P X f →
    Sieve.ofArrows (fun _ : Unit ↦ U) (fun _ ↦ f) ∈ J V}

/-- Every specified cover defines a covering sieve. -/
theorem cover_mem {U V : Obj p P X} (f : U ⟶ V)
    (hf : IsCover p P X f) :
    Sieve.ofArrows (fun _ : Unit ↦ U) (fun _ ↦ f) ∈ topology p P X V := by
  rw [topology, GrothendieckTopology.mem_sInf]
  intro J hJ
  exact hJ U V f hf

/-- Module sheafification exists in the universe of this actual site. -/
instance moduleSheafify :
    HasSheafify (topology p P X) (ModuleCat.{u + 1} P.ring) := by
  let : HasLimits (ModuleCat.{u + 1} P.ring) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, u}
  let : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} P.ring) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, u + 1, u + 1}
      P.ring
  let : PreservesFilteredColimits
      (forget (ModuleCat.{u + 1} P.ring)) :=
    comp_preservesFilteredColimits.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} P.ring) AddCommGrpCat.{u + 1})
      (forget AddCommGrpCat.{u + 1})
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget (ModuleCat.{u + 1} P.ring)) := inferInstance
  infer_instance

/-- The actual structural A-module presheaf, with B on every prism. -/
def structurePresheaf : (Obj p P X)ᵒᵖ ⥤ ModuleCat.{u + 1} P.ring where
  obj U := ModuleCat.of P.ring (ULift.{u + 1} U.unop.prism.ring)
  map f := ModuleCat.ofHom
    { toFun a := ULift.up (f.unop.map.hom a.down)
      map_add' a b := ULift.ext (map_add _ _ _)
      map_smul' a b := ULift.ext ((Hom.linear p P X f.unop).map_smul a
        b.down) }
  map_id _ := by ext a; rfl
  map_comp _ _ := by ext a; rfl

/-- The actual sheafification, rather than a freely named structure sheaf. -/
def structureSheaf : Sheaf (topology p P X)
    (ModuleCat.{u + 1} P.ring) :=
  (presheafToSheaf (topology p P X) _).obj
    (structurePresheaf p P X)

/-- Frobenius lands in restriction of scalars along the actual phi_A. -/
def frobeniusPresheaf : structurePresheaf p P X ⟶
    structurePresheaf p P X ⋙
      ModuleCat.restrictScalars (DeltaRing.frobenius p P.ring) where
  app U := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} P.ring)
    { toFun a := ULift.up
        (DeltaRing.frobenius p U.unop.prism.ring a.down)
      map_add' a b := ULift.ext (map_add _ _ _)
      map_smul' a b := by
        apply ULift.ext
        change DeltaRing.frobenius p U.unop.prism.ring
          (U.unop.base.hom a * b.down) =
          U.unop.base.hom (DeltaRing.frobenius p P.ring a) *
            DeltaRing.frobenius p U.unop.prism.ring b.down
        rw [map_mul, ← BoundedPrisms.Hom.frobenius p U.unop.base] }
  naturality {U V} f := by
    ext a
    apply ULift.ext
    exact (BoundedPrisms.Hom.frobenius p f.unop.map a.down).symm

end MathlibExt.AlgebraicGeometry.RelativePrismaticSite
