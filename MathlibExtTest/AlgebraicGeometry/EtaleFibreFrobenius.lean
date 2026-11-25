/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EtaleFibreFrobenius

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleFibreFrobenius

namespace MathlibExtTest.AlgebraicGeometry.EtaleFibreFrobenius

universe u v w

/-! ### The automorphism topology -/

section Topology

variable {C : Type v} [Category.{w} C] (F : C ⥤ Type u)

-- Component evaluation sends an automorphism to its action on each fibre.
example (σ : Aut F) (X : C) (s : F.obj X) :
    componentEmbedding F σ X s = σ.asIso.hom.app X s :=
  rfl

-- The stabilizer of a point of a fibre is open (each fibre's permutation group is discrete).
example (X : C) (s : F.obj X) :
    @IsOpen (Aut F) (fibreAutomorphismTopology F) {σ | σ.asIso.hom.app X s = s} := by
  let (X : C) : TopologicalSpace (Equiv.Perm (F.obj X)) := ⊥
  have (X : C) : DiscreteTopology (Equiv.Perm (F.obj X)) := ⟨rfl⟩
  have hopen : IsOpen ((fun p : ∀ X, Equiv.Perm (F.obj X) ↦ p X) ⁻¹' {e | e s = s}) :=
    (isOpen_discrete _).preimage (continuous_apply X)
  exact ⟨_, hopen, rfl⟩

example : @IsTopologicalGroup (Aut F) (fibreAutomorphismTopology F) _ :=
  fibreAutomorphismTopologicalGroup F

end Topology

/-! ### Field automorphisms, fibre paths and Frobenius -/

section Fibres

variable {X : Scheme.{u}} {K : Type u} [Field K]

-- The arithmetic fundamental group is a topological group.
example [IsAlgClosed K] (x : Spec (.of K) ⟶ X) :
    IsTopologicalGroup (ArithmeticFundamentalGroup x) :=
  inferInstance

-- `fieldSchemeIso σ` is `Spec` of `σ`, with inverse `Spec` of `σ⁻¹`.
example (σ : K ≃+* K) : (fieldSchemeIso σ).hom = Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  rfl

example (σ : K ≃+* K) : (fieldSchemeIso σ).inv = Spec.map (CommRingCat.ofHom σ.symm.toRingHom) :=
  rfl

-- A scheme automorphism over the point acts on lifts by precomposition.
example (x : Spec (.of K) ⟶ X) (e : Spec (.of K) ≅ Spec (.of K)) (hx : e.hom ≫ x = x)
    (Y : FiniteEtaleOver X) (s : geometricFibre x Y) :
    ((fibreFieldAutomorphism x e hx).asIso.hom.app Y s).1 = e.hom ≫ s.1 :=
  rfl

-- Transport along a fibre path conjugates by the path.
example {x y : Spec (.of K) ⟶ X} (path : fibreFunctor x ≅ fibreFunctor y)
    (σ : Aut (fibreFunctor y)) :
    (transportFibreAutomorphism path σ).asIso = path ≪≫ σ.asIso ≪≫ path.symm :=
  rfl

variable {κ : Type u} [Field κ] [Algebra κ K]

-- Field automorphisms over `κ` act on the lifts of the closed point through a group
-- homomorphism: the action of `σ * τ` is the action of `τ` followed by that of `σ`.
example (y : Spec (.of κ) ⟶ X) (σ τ : K ≃ₐ[κ] K) (Y : FiniteEtaleOver X)
    (s : geometricFibre (closedPointGeometricPoint (K := K) y) Y) :
    ((fibreFieldAutomorphism _ (fieldSchemeIso (σ * τ).toRingEquiv)
        (closedPoint_fixed y (σ * τ))).asIso.hom.app Y s).1 =
      ((fibreFieldAutomorphism _ (fieldSchemeIso σ.toRingEquiv) (closedPoint_fixed y σ) *
        fibreFieldAutomorphism _ (fieldSchemeIso τ.toRingEquiv)
          (closedPoint_fixed y τ)).asIso.hom.app Y s).1 := by
  change Spec.map _ ≫ s.1 = Spec.map _ ≫ (Spec.map _ ≫ s.1)
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

-- The inverse-automorphism element is the action of `σ⁻¹`, transported along the fibre path;
-- on a lift over `y` it precomposes with `Spec` of `σ⁻¹`.
example [IsAlgClosed K] (x : Spec (.of K) ⟶ X) (y : Spec (.of κ) ⟶ X) (σ : K ≃ₐ[κ] K)
    (path : fibreFunctor x ≅ fibreFunctor (closedPointGeometricPoint (K := K) y)) :
    inverseFieldAutomorphismElement x y σ path = transportFibreAutomorphism path
      (fibreFieldAutomorphism _ (fieldSchemeIso σ.symm.toRingEquiv)
        (closedPoint_fixed y σ.symm)) :=
  rfl

-- Geometric Frobenius is that element for a certified arithmetic Frobenius of a finite field.
example [IsAlgClosed K] [Fintype κ] (x : Spec (.of K) ⟶ X) (y : Spec (.of κ) ⟶ X)
    (σ : ArithmeticFrobenius κ K)
    (path : fibreFunctor x ≅ fibreFunctor (closedPointGeometricPoint (K := K) y)) :
    geometricFrobeniusElement x y σ path = inverseFieldAutomorphismElement x y σ.1 path :=
  rfl

-- A certified arithmetic Frobenius really is the `#κ`-power map.
example [Fintype κ] (σ : ArithmeticFrobenius κ K) (a : K) : σ.1 a = a ^ Fintype.card κ :=
  σ.2 a

example (y : Spec (.of κ) ⟶ X) (σ : K ≃ₐ[κ] K) (Y : FiniteEtaleOver X)
    (s : geometricFibre (closedPointGeometricPoint (K := K) y) Y) :
    ((fibreFieldAutomorphism _ (fieldSchemeIso σ.symm.toRingEquiv)
        (closedPoint_fixed y σ.symm)).asIso.hom.app Y s).1 =
      Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ s.1 :=
  rfl

end Fibres

end MathlibExtTest.AlgebraicGeometry.EtaleFibreFrobenius
