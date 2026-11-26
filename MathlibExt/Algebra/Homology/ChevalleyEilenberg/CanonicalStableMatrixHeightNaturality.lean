/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixHeightComparison

/-!
# Independent-algebra naturality of the lifted stable CE colimit

Let k be a commutative ring and f : A → B a unital k-algebra map
between associative algebras in independent worlds v,w. At
H = max(u,v,w,z), entrywise finite matrix maps give a map S^H(f)
between the lifted finite CE colimits and a map C^H(f) between
the lifted CE complexes of Mat_∞(A) and Mat_∞(B).

Let E_A,E_B be the chosen-height finite-to-stable CE isomorphisms.
Their squares satisfy C^H(f) ∘ E_A = E_B ∘ S^H(f) and
E_B⁻¹ ∘ C^H(f) = S^H(f) ∘ E_A⁻¹.
The corresponding square on homology commutes in every degree.
The common height retains the ring and both algebra worlds and
the arbitrary additional height z.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  {B : Type w} [Ring B] [Algebra k B]

/-- For a commutative ring k, a unital k-algebra map f : A → B
and H = max(u,v,w,z), the finite entrywise matrix CE maps induce
S^H(f) : colim_m C_*^H(Mat_m(A)) → colim_m C_*^H(Mat_m(B)).
The algebra carrier worlds v,w are independent. -/
def stableMatrixCoefficientMapAtHeight (f : A →ₐ[k] B) :
    stableMatrixCEComplexAtHeight.{u,v,max u v w z} k A ⟶
      stableMatrixCEComplexAtHeight.{u,w,max u v w z} k B :=
  colimMap (matrixCoefficientNatTransAtHeight.{u,v,w,z} k A f)

/-- For a unital k-algebra map f : A → B and
H = max(u,v,w,z), the induced colimit map S^H(f) satisfies
S^H(f) ∘ ι_(A,m)^H = ι_(B,m)^H ∘ C_*^H(Mat_m(f)).
The equality holds for every finite matrix size m ≥ 0. -/
@[reassoc]
theorem stableMatrixCoefficientMapAtHeight_ι (f : A →ₐ[k] B) (m : ℕ) :
    colimit.ι (matrixComplexFunctorAtHeight.{u,v,max u v w z} k A) m ≫
        stableMatrixCoefficientMapAtHeight.{u,v,w,z} k A f =
      matrixCoefficientMapAtHeight.{u,v,w,z} k A f m ≫
        colimit.ι (matrixComplexFunctorAtHeight.{u,w,max u v w z} k B) m :=
  ι_colimMap (matrixCoefficientNatTransAtHeight.{u,v,w,z} k A f) m

/-- For a commutative ring k, a unital k-algebra map f : A → B
and H = max(u,v,w,z), let E_A,E_B be the chosen-height
finite-to-stable CE isomorphisms. Their forward maps satisfy
C^H(f) ∘ E_A = E_B ∘ S^H(f), from the lifted A-colimit to
the lifted stable Lie CE complex for B. -/
@[reassoc]
theorem canonicalStableMatrixCEIsoAtHeight_naturality (f : A →ₐ[k] B) :
    (canonicalStableMatrixCEIsoAtHeight.{u,v,max u v w z} k A).hom ≫
        canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f =
      stableMatrixCoefficientMapAtHeight.{u,v,w,z} k A f ≫
        (canonicalStableMatrixCEIsoAtHeight.{u,w,max u v w z} k B).hom := by
  apply (colimit.isColimit (matrixComplexFunctorAtHeight.{u,v,max u v w z} k A)).hom_ext
  intro m
  let eA := canonicalStableMatrixCEIsoAtHeight.{u,v,max u v w z} k A
  let eB := canonicalStableMatrixCEIsoAtHeight.{u,w,max u v w z} k B
  let a : matrixComplexAtHeight.{u,v,max u v w z} k A m ⟶
      stableMatrixCEComplexAtHeight.{u,v,max u v w z} k A :=
    colimit.ι (matrixComplexFunctorAtHeight.{u,v,max u v w z} k A) m
  let b : matrixComplexAtHeight.{u,w,max u v w z} k B m ⟶
      stableMatrixCEComplexAtHeight.{u,w,max u v w z} k B :=
    colimit.ι (matrixComplexFunctorAtHeight.{u,w,max u v w z} k B) m
  let c := canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f
  let s := stableMatrixCoefficientMapAtHeight.{u,v,w,z} k A f
  let t := matrixCoefficientMapAtHeight.{u,v,w,z} k A f m
  have hA : a ≫ eA.hom = canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v w z} k A m :=
    colimitToCanonicalStableMatrixCEAtHeight_ι.{u,v,max u v w z} k A m
  have hB : b ≫ eB.hom = canonicalStableMatrixCEInclusionAtHeight.{u,w,max u v w z} k B m :=
    colimitToCanonicalStableMatrixCEAtHeight_ι.{u,w,max u v w z} k B m
  have ht : a ≫ s = t ≫ b := stableMatrixCoefficientMapAtHeight_ι.{u,v,w,z} k A f m
  change a ≫ (eA.hom ≫ c) = a ≫ (s ≫ eB.hom)
  calc
    _ = (a ≫ eA.hom) ≫ c := (Category.assoc a eA.hom c).symm
    _ = canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v w z} k A m ≫ c :=
      congrArg (fun q : matrixComplexAtHeight.{u,v,max u v w z} k A m ⟶
        canonicalStableMatrixCEComplexAtHeight.{u,v,max u v w z} k A => q ≫ c) hA
    _ = t ≫ canonicalStableMatrixCEInclusionAtHeight.{u,w,max u v w z} k B m :=
      canonicalStableMatrixCoefficientCEMapAtHeight_inclusion.{u,v,w,z} k A f m
    _ = t ≫ (b ≫ eB.hom) :=
      congrArg (fun q : matrixComplexAtHeight.{u,w,max u v w z} k B m ⟶
        canonicalStableMatrixCEComplexAtHeight.{u,w,max u v w z} k B => t ≫ q) hB.symm
    _ = (t ≫ b) ≫ eB.hom := (Category.assoc t b eB.hom).symm
    _ = (a ≫ s) ≫ eB.hom :=
      congrArg (fun q : matrixComplexAtHeight.{u,v,max u v w z} k A m ⟶
        stableMatrixCEComplexAtHeight.{u,w,max u v w z} k B => q ≫ eB.hom) ht.symm
    _ = _ := Category.assoc a s eB.hom

/-- For a commutative ring k, a unital k-algebra map f : A → B
and H = max(u,v,w,z), the inverse model comparisons satisfy
E_B⁻¹ ∘ C^H(f) = S^H(f) ∘ E_A⁻¹.
The source is C_*^H(Mat_∞(A)) and the target is the lifted finite
CE colimit for B, with independent algebra worlds. -/
@[reassoc]
theorem canonicalStableMatrixCEIsoAtHeight_inv_naturality (f : A →ₐ[k] B) :
    canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f ≫
        (canonicalStableMatrixCEIsoAtHeight.{u,w,max u v w z} k B).inv =
      (canonicalStableMatrixCEIsoAtHeight.{u,v,max u v w z} k A).inv ≫
        stableMatrixCoefficientMapAtHeight.{u,v,w,z} k A f := by
  apply (cancel_epi (canonicalStableMatrixCEIsoAtHeight.{u,v,max u v w z} k A).hom).1
  rw [← Category.assoc, canonicalStableMatrixCEIsoAtHeight_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- For a commutative ring k, a unital k-algebra map f : A → B,
H = max(u,v,w,z) and n ≥ 0, the homology square satisfies
H_n(C^H(f)) ∘ H_n(E_A) = H_n(E_B) ∘ H_n(S^H(f)).
The comparison maps are the chosen-height finite-to-stable CE
isomorphisms, and the algebra worlds are independent. -/
theorem canonicalStableMatrixCEIsoAtHeight_homology_naturality (f : A →ₐ[k] B) (n : ℕ) :
    HomologicalComplex.homologyMap (canonicalStableMatrixCEIsoAtHeight.{u,v,max u v w z} k A).hom n ≫
        HomologicalComplex.homologyMap
          (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) n =
      HomologicalComplex.homologyMap (stableMatrixCoefficientMapAtHeight.{u,v,w,z} k A f) n ≫
        HomologicalComplex.homologyMap (canonicalStableMatrixCEIsoAtHeight.{u,w,max u v w z} k B).hom n := by
  have h := congrArg (fun q => HomologicalComplex.homologyMap q n)
    (canonicalStableMatrixCEIsoAtHeight_naturality.{u,v,w,z} k A f)
  simpa only [HomologicalComplex.homologyMap_comp] using h

end ChevalleyEilenberg
