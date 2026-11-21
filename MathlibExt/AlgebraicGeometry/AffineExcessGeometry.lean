/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The excess-conormal interface follows AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Chow/GysinLocalCompleteIntersection/
BaseChangeExcessFormula.lean, licensed under Apache 2.0.
Modification notice: extract the affine quotient-ring geometry and use
Mathlib's actual Ideal.mapCotangent and scalar base change; retain the
actual kernel and its dual instead of an unspecified excess bundle.
-/

module
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import MathlibExt.AlgebraicGeometry.ComplexAnalytification
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-!
# Actual affine excess conormal modules and normal bundle spaces

For A → B and I ⊂ A, write J = I B and S = B/J. The displayed map is the
canonical map S ⊗_A I/I² → J/J². The excess conormal is its actual kernel;
the excess normal is the S-linear dual of that kernel. The affine schemes,
quotient base-change maps, symmetric-algebra bundle space and zero section
are constructed directly. The zero section is proved to be a closed immersion.

Smoothness, ranks and the Betti excess comparison are not asserted by these
definitions. Generic algebraic excess formulas already occur in the cited
Axiom source and are not reclassified as missing.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct
namespace MathlibExt.AlgebraicGeometry.AffineExcessGeometry
variable (A B : Type) [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
  [Algebra A B] [IsScalarTower ℂ A B]

def extendedIdeal (I : Ideal A) : Ideal B := I.map (algebraMap A B)

def excessMap (I : Ideal A) :
    (B ⧸ extendedIdeal A B I) ⊗[A] I.Cotangent →ₗ[B ⧸ extendedIdeal A B I]
      (extendedIdeal A B I).Cotangent :=
  letI : IsScalarTower A (B ⧸ extendedIdeal A B I) (extendedIdeal A B I).Cotangent :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      rw [IsScalarTower.algebraMap_apply A B (B ⧸ extendedIdeal A B I)]
      rw [IsScalarTower.algebraMap_smul]
      exact IsScalarTower.algebraMap_smul B r x
  LinearMap.liftBaseChange (B ⧸ extendedIdeal A B I)
    (Ideal.mapCotangent I (extendedIdeal A B I) (Algebra.ofId A B)
      (Ideal.le_comap_map))

abbrev excessConormal (I : Ideal A) := LinearMap.ker (excessMap A B I)
abbrev excessNormal (I : Ideal A) := Module.Dual (B ⧸ extendedIdeal A B I) (excessConormal A B I)

def affine (A : Type) [CommRing A] [Algebra ℂ A] :
    Over (Spec (.of ℂ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
def affineMap : affine B ⟶ affine A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) (by
    simp [affine, ← Spec.map_comp, IsScalarTower.algebraMap_eq ℂ A B])

def quotientMorphism (A : Type) [CommRing A] [Algebra ℂ A] (I : Ideal A) :
    affine (A ⧸ I) ⟶ affine A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (by
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (A ⧸ I)))
    rw [← Spec.map_comp]
    congr 1)

def quotientBaseMap (I : Ideal A) :
    affine (B ⧸ extendedIdeal A B I) ⟶ affine (A ⧸ I) :=
  let q := Ideal.quotientMapₐ (extendedIdeal A B I)
    (IsScalarTower.toAlgHom ℂ A B) Ideal.le_comap_map
  Over.homMk (Spec.map (CommRingCat.ofHom q.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (A ⧸ I))) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (B ⧸ extendedIdeal A B I)))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact q.commutes x)

instance quotientMorphismClosed (A : Type) [CommRing A] [Algebra ℂ A]
    (I : Ideal A) : IsClosedImmersion (quotientMorphism A I).left :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) (Ideal.Quotient.mk_surjective)

variable (S : Type) [CommRing S] [Algebra ℂ S] (E : Type) [AddCommGroup E] [Module S E]

def bundleSpace : Over (Spec (.of ℂ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap S (SymmetricAlgebra S (Module.Dual S E)))) ≫
    (affine S).hom)

def bundleProjection : bundleSpace S E ⟶ affine S :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap S (SymmetricAlgebra S (Module.Dual S E))))) rfl

def zeroSection : affine S ⟶ bundleSpace S E :=
  let a : SymmetricAlgebra S (Module.Dual S E) →ₐ[S] S :=
    SymmetricAlgebra.lift (0 : Module.Dual S E →ₗ[S] S)
  Over.homMk (Spec.map (CommRingCat.ofHom a.toRingHom)) (by
    have h : CommRingCat.ofHom (algebraMap S (SymmetricAlgebra S (Module.Dual S E))) ≫
        CommRingCat.ofHom a.toRingHom = 𝟙 (CommRingCat.of S) := by
      ext x; exact a.commutes x
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (SymmetricAlgebra S (Module.Dual S E)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) =
          Spec.map (CommRingCat.ofHom (algebraMap ℂ S))
    rw [← Category.assoc, ← Spec.map_comp, h, Spec.map_id, Category.id_comp])

instance zeroSectionClosed : IsClosedImmersion (zeroSection S E).left := by
  let a : SymmetricAlgebra S (Module.Dual S E) →ₐ[S] S :=
    SymmetricAlgebra.lift (0 : Module.Dual S E →ₗ[S] S)
  apply IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom a.toRingHom)
  intro x
  exact ⟨algebraMap S (SymmetricAlgebra S (Module.Dual S E)) x, a.commutes x⟩

end MathlibExt.AlgebraicGeometry.AffineExcessGeometry
