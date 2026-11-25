/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixCyclic

/-!
# Coefficient maps of stable matrix Lie algebras

An algebra homomorphism acts entrywise on finite matrix stages and induces a homomorphism of
stable nonunital matrix algebras. Its commutator Lie map induces the corresponding
Chevalley–Eilenberg chain map.

The finite-stage inclusions and colimit comparisons are natural. When the ground ring is a
rational algebra, the stable cyclic-homology maps retain this naturality.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k]

section Algebra

variable (A : Type v) [Ring A] [Algebra k A]
  {B : Type w} [Ring B] [Algebra k B]
  {C : Type z} [Ring C] [Algebra k C]

/-- Direct-limit descent of the entrywise matrix coefficient maps. -/
def canonicalStableMatrixCoefficientAlgHom (f : A →ₐ[k] B) :
    canonicalStableMatrixAlgebra k A →ₙₐ[k] canonicalStableMatrixAlgebra k B :=
  DirectLimit.NonUnitalAlgebra.lift (R := k)
    (G := fun m : ℕ => Matrix (Fin m) (Fin m) A)
    (f := fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
    (P := canonicalStableMatrixAlgebra k B)
    (fun m => (canonicalStableMatrixInclusion k B m).comp
      (f.mapMatrix (m := Fin m)).toNonUnitalAlgHom) (by
        intro m n h x
        change canonicalStableMatrixInclusion k B n
            ((f.mapMatrix (m := Fin n)) (Matrix.zeroExtend h x)) =
          canonicalStableMatrixInclusion k B m ((f.mapMatrix (m := Fin m)) x)
        have hx := Matrix.coefficientLieHom_zeroExtend k A f h x
        change (f.mapMatrix (m := Fin n)) (Matrix.zeroExtend h x) =
          Matrix.zeroExtend h ((f.mapMatrix (m := Fin m)) x) at hx
        rw [hx]
        exact DirectLimit.NonUnitalAlgebra.of_f (R := k)
          (G := fun a : ℕ => Matrix (Fin a) (Fin a) B)
          (f := fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := B) h)
          (i := m) (j := n) h ((f.mapMatrix (m := Fin m)) x))

/-- Every finite stage keeps the entrywise coefficient map. -/
@[simp]
theorem canonicalStableMatrixCoefficientAlgHom_inclusion (f : A →ₐ[k] B)
    (m : ℕ) (x : Matrix (Fin m) (Fin m) A) :
    canonicalStableMatrixCoefficientAlgHom k A f (canonicalStableMatrixInclusion k A m x) =
      canonicalStableMatrixInclusion k B m ((f.mapMatrix (m := Fin m)) x) :=
  DirectLimit.NonUnitalAlgebra.lift_of (R := k)
    (G := fun a : ℕ => Matrix (Fin a) (Fin a) A)
    (f := fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
    (P := canonicalStableMatrixAlgebra k B) _ _ m x

/-- Uniqueness of the direct-limit lift retains the identity coefficient map. -/
theorem canonicalStableMatrixCoefficientAlgHom_id :
    canonicalStableMatrixCoefficientAlgHom k A (AlgHom.id k A) =
      NonUnitalAlgHom.id k (canonicalStableMatrixAlgebra k A) := by
  apply DirectLimit.NonUnitalAlgebra.hom_ext
  intro m
  ext x
  simp only [NonUnitalAlgHom.comp_apply]
  rfl

/-- Uniqueness retains composition across the independent coefficient universes. -/
theorem canonicalStableMatrixCoefficientAlgHom_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    (canonicalStableMatrixCoefficientAlgHom k B g).comp
        (canonicalStableMatrixCoefficientAlgHom k A f) =
      canonicalStableMatrixCoefficientAlgHom k A (g.comp f) := by
  apply DirectLimit.NonUnitalAlgebra.hom_ext
  intro m
  ext x
  simp only [NonUnitalAlgHom.comp_apply]
  rfl

/-- The coefficient map preserves the multiplication-commutator Lie bracket. -/
def canonicalStableMatrixCoefficientLieHom (f : A →ₐ[k] B) :
    canonicalStableMatrixAlgebra k A →ₗ⁅k⁆ canonicalStableMatrixAlgebra k B :=
  (canonicalStableMatrixCoefficientAlgHom k A f).toLieHom

/-- The stable coefficient Lie map retains every finite Lie coefficient map. -/
theorem canonicalStableMatrixCoefficientLieHom_inclusion (f : A →ₐ[k] B) (m : ℕ) :
    (canonicalStableMatrixCoefficientLieHom k A f).comp (canonicalStableMatrixLieInclusion k A m) =
      (canonicalStableMatrixLieInclusion k B m).comp (Matrix.coefficientLieHom k A f m) := by
  apply LieHom.ext
  intro x
  exact canonicalStableMatrixCoefficientAlgHom_inclusion k A f m x

end Algebra

section Complex

variable (A : Type v) [Ring A] [Algebra k A]
  {B : Type v} [Ring B] [Algebra k B]

/-- The CE functor applied to the canonical stable coefficient Lie map. -/
def canonicalStableMatrixCoefficientCEMap (f : A →ₐ[k] B) :
    canonicalStableMatrixCEComplex k A ⟶ canonicalStableMatrixCEComplex k B :=
  nativeComplexMap k (canonicalStableMatrixAlgebra k A)
    (canonicalStableMatrixCoefficientLieHom k A f)

/-- Finite CE coefficient maps commute with the canonical stable Lie inclusions. -/
@[reassoc]
theorem canonicalStableMatrixCoefficientCEMap_inclusion (f : A →ₐ[k] B) (m : ℕ) :
    canonicalStableMatrixCEInclusion k A m ≫ canonicalStableMatrixCoefficientCEMap k A f =
      matrixCoefficientMap k A f m ≫ canonicalStableMatrixCEInclusion k B m := by
  rw [canonicalStableMatrixCEInclusion, canonicalStableMatrixCoefficientCEMap,
    matrixCoefficientMap, canonicalStableMatrixCEInclusion,
    nativeComplexMap_comp, nativeComplexMap_comp,
    canonicalStableMatrixCoefficientLieHom_inclusion]

/-- The canonical CE model isomorphism preserves the coefficient maps. -/
@[reassoc]
theorem canonicalStableMatrixCEIso_naturality (f : A →ₐ[k] B) :
    (canonicalStableMatrixCEIso k A).hom ≫ canonicalStableMatrixCoefficientCEMap k A f =
      stableMatrixCoefficientMap k A f ≫ (canonicalStableMatrixCEIso k B).hom := by
  apply (colimit.isColimit (matrixComplexFunctor k A)).hom_ext
  intro m
  let eA := canonicalStableMatrixCEIso k A
  let eB := canonicalStableMatrixCEIso k B
  let a : matrixComplex k A m ⟶ stableMatrixCEComplex k A :=
    colimit.ι (matrixComplexFunctor k A) m
  let b : matrixComplex k B m ⟶ stableMatrixCEComplex k B :=
    colimit.ι (matrixComplexFunctor k B) m
  let c := canonicalStableMatrixCoefficientCEMap k A f
  let s := stableMatrixCoefficientMap k A f
  let t := matrixCoefficientMap k A f m
  have hA : a ≫ eA.hom = canonicalStableMatrixCEInclusion k A m :=
    colimitToCanonicalStableMatrixCE_ι k A m
  have hB : b ≫ eB.hom = canonicalStableMatrixCEInclusion k B m :=
    colimitToCanonicalStableMatrixCE_ι k B m
  have ht : a ≫ s = t ≫ b := stableMatrixCoefficientMap_ι k A f m
  change a ≫ (eA.hom ≫ c) = a ≫ (s ≫ eB.hom)
  calc
    _ = (a ≫ eA.hom) ≫ c := (Category.assoc a eA.hom c).symm
    _ = canonicalStableMatrixCEInclusion k A m ≫ c :=
      congrArg (fun q : matrixComplex k A m ⟶ canonicalStableMatrixCEComplex k A => q ≫ c) hA
    _ = t ≫ canonicalStableMatrixCEInclusion k B m :=
      canonicalStableMatrixCoefficientCEMap_inclusion k A f m
    _ = t ≫ (b ≫ eB.hom) :=
      congrArg (fun q : matrixComplex k B m ⟶ canonicalStableMatrixCEComplex k B => t ≫ q) hB.symm
    _ = (t ≫ b) ≫ eB.hom := (Category.assoc t b eB.hom).symm
    _ = (a ≫ s) ≫ eB.hom :=
      congrArg (fun q : matrixComplex k A m ⟶ stableMatrixCEComplex k B => q ≫ eB.hom) ht.symm
    _ = _ := Category.assoc a s eB.hom

/-- The inverse of the model isomorphism preserves the same coefficient square. -/
@[reassoc]
theorem canonicalStableMatrixCEIso_inv_naturality (f : A →ₐ[k] B) :
    canonicalStableMatrixCoefficientCEMap k A f ≫ (canonicalStableMatrixCEIso k B).inv =
      (canonicalStableMatrixCEIso k A).inv ≫ stableMatrixCoefficientMap k A f := by
  apply (cancel_epi (canonicalStableMatrixCEIso k A).hom).1
  rw [← Category.assoc, canonicalStableMatrixCEIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

section Rational

variable [Algebra ℚ k]

/-- The HC map on canonical stable matrix CE homology retains coefficient naturality. -/
theorem canonicalStableMatrixCyclicHomologyMap_naturality (f : A →ₐ[k] B) (n : ℕ) :
    HomologicalComplex.homologyMap (canonicalStableMatrixCoefficientCEMap k A f) (n + 1) ≫
        canonicalStableMatrixCyclicHomologyMap k B n =
      canonicalStableMatrixCyclicHomologyMap k A n ≫
        ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomologyMap f.toNonUnitalAlgHom n := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g (n + 1))
    (canonicalStableMatrixCEIso_inv_naturality k A f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  rw [canonicalStableMatrixCyclicHomologyMap, canonicalStableMatrixCyclicHomologyMap,
    ← Category.assoc, h, Category.assoc, stableMatrixCyclicHomologyMap_naturality]
  exact (Category.assoc (HomologicalComplex.homologyMap (canonicalStableMatrixCEIso k A).inv (n + 1))
    (stableMatrixCyclicHomologyMap k A n)
    (ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomologyMap f.toNonUnitalAlgHom n)).symm

end Rational
end Complex
end ChevalleyEilenberg
