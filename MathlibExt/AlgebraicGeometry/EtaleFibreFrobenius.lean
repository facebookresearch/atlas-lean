/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleProper.lean`,
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/EtaleFundamentalGroup.lean` and
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/AutomorphismTopology.lean`
(AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b; these files carry no
individual author or copyright notice):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modified: retain actual finite étale covers and lift-valued fibre functors; specialize
permutation topologies to discrete finite fibres and normalize Frobenius by field automorphisms
and actual geometric fibre paths.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Instances.Discrete

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual finite étale fibre functors and normalized Frobenius

The arithmetic étale fundamental group is Aut of the genuine finite étale
geometric fibre functor. Frobenius at a closed point acts by precomposing
actual lifts Spec K -> Y with Spec of the inverse q-power automorphism.
A geometric fibre path transports this automorphism to the base fibre.
No abstract fundamental-group carrier or freely chosen Frobenius is used.

References: Stacks Project, Tags 0BNC, 0BMR and 03SV; SGA 1, V, §7.
-/

namespace MathlibExt.AlgebraicGeometry.EtaleFibreFrobenius

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u v w

/-- The actual morphism property finite and étale. -/
abbrev finiteEtale : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

/-- The actual category of finite étale covers of X. -/
abbrev FiniteEtaleOver (X : Scheme.{u}) :=
  MorphismProperty.Over (finiteEtale : MorphismProperty Scheme.{u}) ⊤ X

/-- Actual lifts of a geometric point to a finite étale cover. -/
abbrev geometricFibre {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ X) (Y : FiniteEtaleOver X) :=
  {s : Spec (.of K) ⟶ Y.left // s ≫ Y.hom = x}

/-- The genuine finite étale geometric fibre functor. -/
def fibreFunctor {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ X) : FiniteEtaleOver X ⥤ Type u where
  obj Y := geometricFibre x Y
  map {Y Z} f := ↾ (fun s ↦ ⟨s.1 ≫ f.left, by
    rw [Category.assoc, MorphismProperty.Over.w f, s.2]⟩)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- Actual automorphisms of a finite étale geometric fibre functor. -/
abbrev ArithmeticFundamentalGroup {X : Scheme.{u}} {K : Type u} [Field K]
    [IsAlgClosed K] (x : Spec (.of K) ⟶ X) := Aut (fibreFunctor x)

section AutomorphismTopology

variable {C : Type v} [Category.{w} C] (F : C ⥤ Type u)

/-- Evaluation of actual natural automorphisms on all fibres. -/
def componentEmbedding : Aut F →* ∀ X, Equiv.Perm (F.obj X) :=
  MonoidHom.mk' (fun σ X ↦ (σ.asIso.app X).toEquiv) (fun _ _ ↦ rfl)

/-- The product of the discrete topologies on the permutation groups of the fibres. When every
fibre is finite (as for finite étale covers), this gives the profinite topology on `Aut F`;
for a functor with infinite fibres it is not the topology of pointwise convergence. -/
@[instance_reducible]
def fibrePermutationTopology : TopologicalSpace (∀ X, Equiv.Perm (F.obj X)) := by
  let (X : C) : TopologicalSpace (Equiv.Perm (F.obj X)) := ⊥
  exact inferInstance

/-- The topology on `Aut F` induced by the action on all fibres, each permutation group being
discrete; for finite fibres the finite intersections of stabilizers of points form a basis of
neighbourhoods of `1`. -/
@[instance_reducible]
def fibreAutomorphismTopology : TopologicalSpace (Aut F) :=
  TopologicalSpace.induced (componentEmbedding F) (fibrePermutationTopology F)

theorem fibreAutomorphismTopologicalGroup :
    @IsTopologicalGroup (Aut F) (fibreAutomorphismTopology F) _ := by
  let (X : C) : TopologicalSpace (Equiv.Perm (F.obj X)) := ⊥
  let (X : C) : DiscreteTopology (Equiv.Perm (F.obj X)) := ⟨rfl⟩
  change @IsTopologicalGroup (Aut F)
    (TopologicalSpace.induced (componentEmbedding F) inferInstance) _
  exact isTopologicalGroup_induced (componentEmbedding F)

end AutomorphismTopology

instance fundamentalGroupTopology {X : Scheme.{u}} {K : Type u} [Field K]
    [IsAlgClosed K] (x : Spec (.of K) ⟶ X) :
    TopologicalSpace (ArithmeticFundamentalGroup x) :=
  fibreAutomorphismTopology (fibreFunctor x)

instance fundamentalGroupTopologicalGroup {X : Scheme.{u}} {K : Type u} [Field K]
    [IsAlgClosed K] (x : Spec (.of K) ⟶ X) :
    IsTopologicalGroup (ArithmeticFundamentalGroup x) :=
  fibreAutomorphismTopologicalGroup (fibreFunctor x)

/-- Spec of an actual field automorphism, with its actual inverse. -/
def fieldSchemeIso {K : Type u} [Field K] (σ : K ≃+* K) : Spec (.of K) ≅ Spec (.of K) where
  hom := Spec.map (CommRingCat.ofHom σ.toRingHom)
  inv := Spec.map (CommRingCat.ofHom σ.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of K) using 1
    congr 1
    ext a
    exact σ.apply_symm_apply a
  inv_hom_id := by
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of K) using 1
    congr 1
    ext a
    exact σ.symm_apply_apply a

/-- The lift action is precomposition by the displayed scheme automorphism. -/
def fibreFieldAutomorphism {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ X) (e : Spec (.of K) ≅ Spec (.of K))
    (hx : e.hom ≫ x = x) : Aut (fibreFunctor x) := by
  have hi : e.inv ≫ x = x := by
    apply (cancel_epi e.hom).1
    simp [← Category.assoc, hx]
  refine Aut.of ?_
  refine
    { hom :=
        { app Y := ↾ (fun s : geometricFibre x Y ↦
            ⟨e.hom ≫ s.1, by rw [Category.assoc, s.2, hx]⟩)
          naturality Y Z f := by
            ext s
            apply Subtype.ext
            change e.hom ≫ (s.1 ≫ f.left) = (e.hom ≫ s.1) ≫ f.left
            exact (Category.assoc _ _ _).symm }
      inv :=
        { app Y := ↾ (fun s : geometricFibre x Y ↦
            ⟨e.inv ≫ s.1, by rw [Category.assoc, s.2, hi]⟩)
          naturality Y Z f := by
            ext s
            apply Subtype.ext
            change e.inv ≫ (s.1 ≫ f.left) = (e.inv ≫ s.1) ≫ f.left
            exact (Category.assoc _ _ _).symm }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext Y s
    apply Subtype.ext
    change e.inv ≫ (e.hom ≫ s.1) = s.1
    simp [← Category.assoc]
  · ext Y s
    apply Subtype.ext
    change e.hom ≫ (e.inv ≫ s.1) = s.1
    simp [← Category.assoc]

/-- Transport through an actual isomorphism of geometric fibre functors. -/
def transportFibreAutomorphism {X : Scheme.{u}} {K : Type u} [Field K]
    {x y : Spec (.of K) ⟶ X} (path : fibreFunctor x ≅ fibreFunctor y)
    (σ : Aut (fibreFunctor y)) : Aut (fibreFunctor x) :=
  Aut.of (path ≪≫ σ.asIso ≪≫ path.symm)

/-- The geometric point `Spec K → Spec κ → X` over a `κ`-valued point `y` of `X` (for instance a
closed point with residue field `κ`). -/
abbrev closedPointGeometricPoint {X : Scheme.{u}} {κ K : Type u}
    [Field κ] [Field K] [Algebra κ K] (y : Spec (.of κ) ⟶ X) : Spec (.of K) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ y

/-- A κ-automorphism of K fixes the displayed geometric point over Spec κ. -/
theorem closedPoint_fixed {X : Scheme.{u}} {κ K : Type u}
    [Field κ] [Field K] [Algebra κ K] (y : Spec (.of κ) ⟶ X) (σ : K ≃ₐ[κ] K) :
    (fieldSchemeIso σ.toRingEquiv).hom ≫ closedPointGeometricPoint (K := K) y =
      closedPointGeometricPoint (K := K) y := by
  have h : CommRingCat.ofHom (algebraMap κ K) ≫
      CommRingCat.ofHom σ.toRingHom = CommRingCat.ofHom (algebraMap κ K) := by
    ext a
    exact σ.commutes a
  change Spec.map _ ≫ (Spec.map _ ≫ y) = Spec.map _ ≫ y
  rw [← Category.assoc, ← Spec.map_comp, h]

/-- The action of the inverse of a field automorphism `σ` of `K` over `κ` on the lifts of the
geometric point over `y`, transported to the base fibre through a geometric fibre path. For the
arithmetic Frobenius `σ` this is geometric Frobenius (`geometricFrobeniusElement`). -/
def inverseFieldAutomorphismElement {X : Scheme.{u}} {κ K : Type u}
    [Field κ] [Field K] [Algebra κ K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ X) (y : Spec (.of κ) ⟶ X) (σ : K ≃ₐ[κ] K)
    (path : fibreFunctor x ≅ fibreFunctor (closedPointGeometricPoint (K := K) y)) :
    ArithmeticFundamentalGroup x :=
  transportFibreAutomorphism path
    (fibreFieldAutomorphism (closedPointGeometricPoint (K := K) y)
      (fieldSchemeIso σ.symm.toRingEquiv) (closedPoint_fixed y σ.symm))

/-- Arithmetic Frobenius of a finite field `κ` acting on an extension field `K`: an automorphism
of `K` over `κ` that raises every element to the power `#κ`. -/
def ArithmeticFrobenius (κ K : Type u) [Field κ] [Fintype κ] [Field K] [Algebra κ K] :=
  {σ : K ≃ₐ[κ] K // ∀ a : K, σ a = a ^ Fintype.card κ}

/-- Geometric Frobenius: `Spec` of the inverse of the arithmetic `#κ`-power automorphism, acting
on the lifts of the geometric point over `y` and transported through the geometric fibre path. -/
def geometricFrobeniusElement {X : Scheme.{u}} {κ K : Type u}
    [Field κ] [Fintype κ] [Field K] [Algebra κ K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ X) (y : Spec (.of κ) ⟶ X) (σ : ArithmeticFrobenius κ K)
    (path : fibreFunctor x ≅ fibreFunctor (closedPointGeometricPoint (K := K) y)) :
    ArithmeticFundamentalGroup x :=
  inverseFieldAutomorphismElement x y σ.1 path

end MathlibExt.AlgebraicGeometry.EtaleFibreFrobenius
