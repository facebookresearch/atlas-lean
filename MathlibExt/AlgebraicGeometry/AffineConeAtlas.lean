/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
/-!
# Actual affine POT cone algebras and quotient presentations

The normal-cone algebra is B⊗_P Rees(ker(P→B)), canonically the associated
normal cone. The degree-one cotangent map and the finite-free comparison
complex are constructed. A split degree-zero presentation gives the atlas
normal cone × (ker φ⁰)^∨; its map into (E⁻¹)^∨ is the actual sum of the
conormal map and the projected differential. No cone carrier is supplied.

Atlas points are algebra homomorphisms from this actual coordinate ring.
Their morphisms are the actual E⁰-dual translations of the displayed matrix
coordinates. Groupoid laws are proved. Closedness, image stability and
intrinsic compatibility remain geometric comparison work, not assumptions
of a freely named virtual class.

The construction uses Mathlib's Rees algebra (`Mathlib.RingTheory.ReesAlgebra`) and the
cotangent complex of an algebra extension (`Mathlib.RingTheory.Extension.Cotangent.Basic`).
Virtual classes for a chosen immersion are constructed in AxiomMath/Stacks
(revision c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/Chow/BivariantLemmas/VirtualNormalBundleClassConstruction.lean`)
and are not requested here.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AffineConeAtlas
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
variable {k B : Type} [CommRing k] [CommRing B] [Algebra k B]

abbrev normalAlgebra (P : _root_.Algebra.Extension.{0} k B) := B ⊗[P.Ring] reesAlgebra P.ker

def degreeOne (P : _root_.Algebra.Extension.{0} k B) : P.ker →ₗ[P.Ring] reesAlgebra P.ker where
  toFun x := ⟨Polynomial.monomial 1 x.1,
    reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using x.2)⟩
  map_add' x y := by apply Subtype.ext; exact (Polynomial.monomial 1).map_add x.1 y.1
  map_smul' r x := by apply Subtype.ext; exact (Polynomial.monomial 1).map_smul r x.1

def normalDegreeOne (P : _root_.Algebra.Extension.{0} k B) : P.ker →ₗ[P.Ring] normalAlgebra P :=
  (Algebra.TensorProduct.includeRight.toLinearMap.restrictScalars P.Ring) ∘ₗ degreeOne P

theorem normalDegreeOne_mul (P : _root_.Algebra.Extension.{0} k B) (x y : P.ker) :
    normalDegreeOne P (x * y) = 0 := by
  have he : degreeOne P (x * y) = (x.1 : P.Ring) • degreeOne P y := by
    apply Subtype.ext
    change Polynomial.monomial 1 (x.1 * y.1) = x.1 • Polynomial.monomial 1 y.1
    rw [← smul_eq_mul, map_smul]
  rw [normalDegreeOne, LinearMap.comp_apply, he, map_smul]
  have hx : algebraMap P.Ring B x.1 = 0 := x.2
  rw [← IsScalarTower.algebraMap_smul B, hx, zero_smul]

def normalCotangentR (P : _root_.Algebra.Extension.{0} k B) :
    P.ker.Cotangent →ₗ[P.Ring] normalAlgebra P :=
  Ideal.Cotangent.lift (normalDegreeOne P) (normalDegreeOne_mul P)

def normalCotangent (P : _root_.Algebra.Extension.{0} k B) : P.Cotangent →ₗ[B] normalAlgebra P :=
  let f : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' := _root_.Algebra.Extension.Cotangent.val_smul' }
  (normalCotangentR P ∘ₗ f.toLinearMap).extendScalarsOfSurjective P.algebraMap_surjective

structure ConePresentation (P : _root_.Algebra.Extension.{0} k B) where
  negativeRank : ℕ
  zeroRank : ℕ
  differential : (Fin negativeRank → B) →ₗ[B] (Fin zeroRank → B)
  negativeMap : (Fin negativeRank → B) →ₗ[B] P.Cotangent
  zeroMap : (Fin zeroRank → B) →ₗ[B] P.CotangentSpace
  comm : P.cotangentComplex ∘ₗ negativeMap = zeroMap ∘ₗ differential
  splitting : P.CotangentSpace →ₗ[B] (Fin zeroRank → B)
  split : zeroMap ∘ₗ splitting = LinearMap.id

def modelComplex {P : _root_.Algebra.Extension.{0} k B} (F : ConePresentation P) :
    CochainComplex (ModuleCat.{0} B) ℤ :=
  MathlibExt.AlgebraicGeometry.AffineObstructionComplexes.complex B
    ⟨F.negativeRank, F.zeroRank, F.differential⟩

def cotangentComplex (P : _root_.Algebra.Extension.{0} k B) : CochainComplex (ModuleCat.{0} B) ℤ :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map
    (ModuleCat.ofHom P.cotangentComplex))

def comparisonCochain {P : _root_.Algebra.Extension.{0} k B} (F : ConePresentation P) :
    modelComplex F ⟶ cotangentComplex P :=
  CochainComplex.mappingCone.map _ _
    ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom F.negativeMap))
    ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom F.zeroMap)) (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact ModuleCat.hom_ext F.comm.symm)

def IsObstructionTheory {P : _root_.Algebra.Extension.{0} k B} (F : ConePresentation P) : Prop :=
  IsIso (HomologicalComplex.homologyMap (comparisonCochain F) 0) ∧
    Epi (HomologicalComplex.homologyMap (comparisonCochain F) (-1))

variable {P : _root_.Algebra.Extension.{0} k B}

def excessProjection (F : ConePresentation P) :
    (Fin F.zeroRank → B) →ₗ[B] LinearMap.ker F.zeroMap where
  toFun x := ⟨x - F.splitting (F.zeroMap x), by
    change F.zeroMap (x - F.splitting (F.zeroMap x)) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun F.split (F.zeroMap x)
    exact sub_eq_zero.mpr h.symm⟩
  map_add' x y := by ext; simp [map_add, add_sub_add_comm]
  map_smul' r x := by ext; simp [map_smul, smul_sub]

abbrev atlasAlgebra (F : ConePresentation P) :=
  normalAlgebra P ⊗[B] SymmetricAlgebra B (LinearMap.ker F.zeroMap)

def atlasHom (F : ConePresentation P) :
    SymmetricAlgebra B (Fin F.negativeRank → B) →ₐ[B] atlasAlgebra F := by
  let f : (Fin F.negativeRank → B) →ₗ[B] atlasAlgebra F :=
    (Algebra.TensorProduct.includeLeft.toLinearMap ∘ₗ normalCotangent P ∘ₗ F.negativeMap) +
      (Algebra.TensorProduct.includeRight.toLinearMap ∘ₗ
        SymmetricAlgebra.ι B (LinearMap.ker F.zeroMap) ∘ₗ excessProjection F ∘ₗ F.differential)
  exact SymmetricAlgebra.lift (R := B) (M := Fin F.negativeRank → B) (A := atlasAlgebra F) f

variable (F : ConePresentation P) (C : Type) [CommRing C] [Algebra B C]

structure AtlasPoint where
  map : atlasAlgebra F →ₐ[B] C

def coordinates (a : AtlasPoint F C) : (Fin F.negativeRank → B) →ₗ[B] C :=
  a.map.toLinearMap ∘ₗ (atlasHom F).toLinearMap ∘ₗ SymmetricAlgebra.ι B _

structure AtlasHom (a b : AtlasPoint F C) where
  translation : (Fin F.zeroRank → B) →ₗ[B] C
  relation : coordinates F C b = coordinates F C a + translation ∘ₗ F.differential

instance : Groupoid (AtlasPoint F C) where
  Hom := AtlasHom F C
  id a := ⟨0, by simp⟩
  comp f g := ⟨f.translation + g.translation, by
    rw [g.relation, f.relation]
    simp [LinearMap.add_comp, add_assoc]⟩
  inv f := ⟨-f.translation, by
    rw [f.relation]
    simp⟩
  id_comp f := by cases f; congr; exact zero_add _
  comp_id f := by cases f; congr; exact add_zero _
  assoc f g h := by cases f; cases g; cases h; congr 1; exact add_assoc _ _ _
  inv_comp f := by cases f; congr; exact neg_add_cancel _

@[ext] theorem atlasHom_ext {a b : AtlasPoint F C} {f g : a ⟶ b}
    (h : f.translation = g.translation) : f = g := by cases f; cases g; cases h; rfl

/-- Actual base change of affine cone points and tangent translations along
a coefficient algebra homomorphism. -/
def coefficientFunctor {D : Type} [CommRing D] [Algebra B D] (h : C →ₐ[B] D) :
    AtlasPoint F C ⥤ AtlasPoint F D where
  obj a := ⟨h.comp a.map⟩
  map f := ⟨h.toLinearMap ∘ₗ f.translation, by
    change h.toLinearMap ∘ₗ coordinates F C _ =
      h.toLinearMap ∘ₗ coordinates F C _ + (h.toLinearMap ∘ₗ f.translation) ∘ₗ F.differential
    rw [f.relation, LinearMap.comp_add, LinearMap.comp_assoc]⟩
  map_id a := by
    apply atlasHom_ext
    change h.toLinearMap ∘ₗ (0 : (Fin F.zeroRank → B) →ₗ[B] C) = 0
    exact LinearMap.comp_zero _
  map_comp f g := by apply atlasHom_ext; ext x; exact h.toLinearMap.map_add _ _

/-- Change only the chosen degree-zero splitting; the POT maps stay fixed. -/
def changeSplitting (s : P.CotangentSpace →ₗ[B] (Fin F.zeroRank → B))
    (h : F.zeroMap ∘ₗ s = LinearMap.id) : ConePresentation P :=
  { F with splitting := s, split := h }

/-- An actual acyclic finite-free stabilization, with comparison maps to the
same cotangent presentation fixed by the displayed matrix equations. -/
structure AcyclicStabilization (G : ConePresentation P) (c : ℕ)
    (μ : (Fin c → B) →ₗ[B] P.Cotangent) where
  negativeRank : G.negativeRank = F.negativeRank + c
  zeroRank : G.zeroRank = F.zeroRank + c
  negativeIso : (Fin G.negativeRank → B) ≃ₗ[B]
    ((Fin F.negativeRank → B) × (Fin c → B))
  zeroIso : (Fin G.zeroRank → B) ≃ₗ[B] ((Fin F.zeroRank → B) × (Fin c → B))
  differential : zeroIso.toLinearMap ∘ₗ G.differential =
    ((F.differential ∘ₗ LinearMap.fst B _ _).prod (LinearMap.snd B _ _)) ∘ₗ
      negativeIso.toLinearMap
  negativeMap : G.negativeMap =
    (F.negativeMap ∘ₗ LinearMap.fst B _ _ + μ ∘ₗ LinearMap.snd B _ _) ∘ₗ
      negativeIso.toLinearMap
  zeroMap : G.zeroMap =
    (F.zeroMap ∘ₗ LinearMap.fst B _ _ + P.cotangentComplex ∘ₗ μ ∘ₗ
      LinearMap.snd B _ _) ∘ₗ zeroIso.toLinearMap

end MathlibExt.AlgebraicGeometry.AffineConeAtlas
