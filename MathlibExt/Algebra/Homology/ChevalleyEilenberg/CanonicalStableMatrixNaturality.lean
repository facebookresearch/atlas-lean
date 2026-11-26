/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixCyclic

/-!
# Algebra maps on stable matrix Lie algebras and their CE models

Let k be a commutative ring and f : A → B a unital map of associative
k-algebras. Entrywise finite matrix maps descend to the nonunital
algebra map Mat_∞(f), hence to a commutator Lie map. They preserve
identities and composition and commute with all finite inclusions.
These algebra and Lie maps allow independent coefficient-algebra worlds.

For A and B in a common carrier world v, applying CE gives a chain map
C(f) between C_*(Mat_∞(A)) and C_*(Mat_∞(B)) in
ModuleCat^max(u,v)(k). Let S(f) be the map of finite CE colimits and
E_A,E_B the finite-to-stable isomorphisms. Then
C(f)E_A = E_B S(f) and E_B⁻¹ C(f) = S(f)E_A⁻¹.

If k is a ℚ-algebra, the stable trace maps
Θ_(A,n) : H_(n+1)(Mat_∞(A)) → HC_n(A)
satisfy Θ_(B,n) ∘ H_(n+1)(C(f)) = HC_n(f) ∘ Θ_(A,n).
The chain and homology statements retain the indicated common
coefficient-carrier world.
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

/-- For a commutative ring k and a unital k-algebra map
f : A → B, applying f entrywise in every finite matrix stage
induces Mat_∞(f) : Mat_∞(A) →ₙₐ[k] Mat_∞(B).
The algebra carrier worlds may be independent. -/
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

/-- For a unital k-algebra map f : A → B and a matrix
X ∈ Mat_m(A), the induced stable algebra map satisfies
Mat_∞(f)(i_(A,m)(X)) = i_(B,m)(Mat_m(f)(X)).
Here Mat_m(f) applies f entrywise and i_m is the finite-stage
stable inclusion. -/
@[simp]
theorem canonicalStableMatrixCoefficientAlgHom_inclusion (f : A →ₐ[k] B)
    (m : ℕ) (x : Matrix (Fin m) (Fin m) A) :
    canonicalStableMatrixCoefficientAlgHom k A f (canonicalStableMatrixInclusion k A m x) =
      canonicalStableMatrixInclusion k B m ((f.mapMatrix (m := Fin m)) x) :=
  DirectLimit.NonUnitalAlgebra.lift_of (R := k)
    (G := fun a : ℕ => Matrix (Fin a) (Fin a) A)
    (f := fun _ _ h => Matrix.zeroExtendAlgHom (k := k) (A := A) h)
    (P := canonicalStableMatrixAlgebra k B) _ _ m x

/-- For a commutative ring k and an associative unital
k-algebra A, the stable nonunital algebra map induced by
id_A is id_(Mat_∞(A)). -/
theorem canonicalStableMatrixCoefficientAlgHom_id :
    canonicalStableMatrixCoefficientAlgHom k A (AlgHom.id k A) =
      NonUnitalAlgHom.id k (canonicalStableMatrixAlgebra k A) := by
  apply DirectLimit.NonUnitalAlgebra.hom_ext
  intro m
  ext x
  simp only [NonUnitalAlgHom.comp_apply]
  rfl

/-- For a commutative ring k and unital k-algebra maps
f : A → B and g : B → C, the stable nonunital maps satisfy
Mat_∞(g) ∘ Mat_∞(f) = Mat_∞(g ∘ f).
The carrier worlds of all three coefficient algebras may be independent. -/
theorem canonicalStableMatrixCoefficientAlgHom_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    (canonicalStableMatrixCoefficientAlgHom k B g).comp
        (canonicalStableMatrixCoefficientAlgHom k A f) =
      canonicalStableMatrixCoefficientAlgHom k A (g.comp f) := by
  apply DirectLimit.NonUnitalAlgebra.hom_ext
  intro m
  ext x
  simp only [NonUnitalAlgHom.comp_apply]
  rfl

/-- For a commutative ring k and a unital k-algebra map
f : A → B, the stable nonunital algebra map Mat_∞(f) preserves
[X,Y] = XY−YX and is a k-Lie homomorphism
Mat_∞(A) → Mat_∞(B), across independent algebra worlds. -/
def canonicalStableMatrixCoefficientLieHom (f : A →ₐ[k] B) :
    canonicalStableMatrixAlgebra k A →ₗ⁅k⁆ canonicalStableMatrixAlgebra k B :=
  (canonicalStableMatrixCoefficientAlgHom k A f).toLieHom

/-- For a unital k-algebra map f : A → B and m ≥ 0, the
stable Lie coefficient map satisfies
Mat_∞(f) ∘ i_(A,m) = i_(B,m) ∘ Mat_m(f)
as Lie homomorphisms. The finite and stable brackets are
multiplication commutators. -/
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

/-- For a commutative ring k and a unital k-algebra map
f : A → B with A,B in the same carrier world v, applying CE
to Mat_∞(f) gives C_*(Mat_∞(A)) → C_*(Mat_∞(B)).
Its degree-n map is ⋀^n Mat_∞(f), in ModuleCat^max(u,v)(k). -/
def canonicalStableMatrixCoefficientCEMap (f : A →ₐ[k] B) :
    canonicalStableMatrixCEComplex k A ⟶ canonicalStableMatrixCEComplex k B :=
  nativeComplexMap k (canonicalStableMatrixAlgebra k A)
    (canonicalStableMatrixCoefficientLieHom k A f)

/-- For a commutative ring k, a unital k-algebra map f : A → B
in a common carrier world and m ≥ 0, the chain maps satisfy
C(f) ∘ C(i_(A,m)) = C(i_(B,m)) ∘ C(Mat_m(f)).
Thus the stable CE coefficient map restricts to the finite
entrywise coefficient map at every matrix stage. -/
@[reassoc]
theorem canonicalStableMatrixCoefficientCEMap_inclusion (f : A →ₐ[k] B) (m : ℕ) :
    canonicalStableMatrixCEInclusion k A m ≫ canonicalStableMatrixCoefficientCEMap k A f =
      matrixCoefficientMap k A f m ≫ canonicalStableMatrixCEInclusion k B m := by
  rw [canonicalStableMatrixCEInclusion, canonicalStableMatrixCoefficientCEMap,
    matrixCoefficientMap, canonicalStableMatrixCEInclusion,
    nativeComplexMap_comp, nativeComplexMap_comp,
    canonicalStableMatrixCoefficientLieHom_inclusion]

/-- For a commutative ring k and a unital k-algebra map
f : A → B in a common carrier world, let E_A,E_B be the
finite-to-stable CE isomorphisms, S(f) the finite-colimit map and
C(f) the stable Lie CE map. Then C(f) ∘ E_A = E_B ∘ S(f)
as chain maps from the A-colimit to the stable B-complex. -/
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

/-- For a commutative ring k and a unital k-algebra map
f : A → B in a common carrier world, the inverse model maps satisfy
E_B⁻¹ ∘ C(f) = S(f) ∘ E_A⁻¹.
The source is the CE complex of Mat_∞(A) and the target is the
finite matrix CE colimit for B. -/
@[reassoc]
theorem canonicalStableMatrixCEIso_inv_naturality (f : A →ₐ[k] B) :
    canonicalStableMatrixCoefficientCEMap k A f ≫ (canonicalStableMatrixCEIso k B).inv =
      (canonicalStableMatrixCEIso k A).inv ≫ stableMatrixCoefficientMap k A f := by
  apply (cancel_epi (canonicalStableMatrixCEIso k A).hom).1
  rw [← Category.assoc, canonicalStableMatrixCEIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

section Rational

variable [Algebra ℚ k]

/-- For a commutative ℚ-algebra k and a unital k-algebra map
f : A → B in a common carrier world, the stable trace maps satisfy
Θ_(B,n) ∘ H_(n+1)(C(f)) = HC_n(f) ∘ Θ_(A,n) for every n ≥ 0.
The source is stable matrix Lie homology for A in degree n+1,
and the target is cyclic homology of B in degree n. -/
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
