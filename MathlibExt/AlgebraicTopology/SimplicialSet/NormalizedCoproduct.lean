/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateEmbedding

/-!
# Coproduct descriptions of normalized chains

Identifies each degree of normalized simplicial chains with a coproduct of
coefficient objects indexed by nondegenerate simplices. Computes the coproduct
injections and proves naturality for monomorphisms of simplicial sets.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (X : SSet.{w}) (R : C) (n : ℕ)

/-- The canonical isomorphism from the explicit coproduct of copies of `R`
indexed by `X.nonDegenerate n` to `(X.normalizedChainComplex R).X n`.

It is defined as the canonical isomorphism between the colimit cocone points
supplied by Mathlib's standard coproduct witness `coproductIsCoproduct` and
`X.isColimitCofanNormalizedChainComplex R n`. This construction uses only the
public colimit API and remains stable if the private implementation of
normalized chains is replaced by an isomorphic one. -/
noncomputable def normalizedChainComplexCoproductIso :
    (∐ fun (_ : X.nonDegenerate n) => R) ≅ (X.normalizedChainComplex R).X n :=
  IsColimit.coconePointUniqueUpToIso
    (s := Cofan.mk (∐ fun (_ : X.nonDegenerate n) => R)
      (Sigma.ι (fun (_ : X.nonDegenerate n) => R)))
    (t := X.cofanNormalizedChainComplex R n)
    (coproductIsCoproduct (fun (_ : X.nonDegenerate n) => R))
    (X.isColimitCofanNormalizedChainComplex R n)

/-- The coproduct injection for a nondegenerate simplex, followed by the forward
map of `normalizedChainComplexCoproductIso`, is the canonical inclusion
`X.ιNormalizedChainComplex` of its underlying simplex. -/
@[reassoc (attr := simp)]
theorem ι_normalizedChainComplexCoproductIso_hom (x : X.nonDegenerate n) :
    Sigma.ι (fun (_ : X.nonDegenerate n) => R) x ≫
      (X.normalizedChainComplexCoproductIso R n).hom =
    X.ιNormalizedChainComplex (R := R) x.val := by
  dsimp [normalizedChainComplexCoproductIso]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (s := Cofan.mk (∐ fun (_ : X.nonDegenerate n) => R)
      (Sigma.ι (fun (_ : X.nonDegenerate n) => R)))
    (t := X.cofanNormalizedChainComplex R n)
    (coproductIsCoproduct (fun (_ : X.nonDegenerate n) => R))
    (X.isColimitCofanNormalizedChainComplex R n) ⟨x⟩

end SSet

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  {X Y : SSet.{w}} (f : X ⟶ Y) [Mono f] (R : C) (n : ℕ)

/-- For a monomorphism `f : X ⟶ Y` of simplicial sets, the normalized chain map
in degree `n`, transported via the canonical coproduct isomorphisms
`normalizedChainComplexCoproductIso`, coincides with coproduct reindexing along
the embedding `nonDegenerateEmbeddingOfMono f n` of nondegenerate simplices.

In other words, the square
```
∐_{X.nonDeg n} R  --iso_X-->  (X.normalizedChainComplex R).X n
      |                                |
sigmaConst.map embedding          (normalizedChainComplexMap f R).f n
      v                                v
∐_{Y.nonDeg n} R  --iso_Y-->  (Y.normalizedChainComplex R).X n
```
commutes, i.e. source coproduct to source normalized chains to target
normalized chains equals source coproduct reindexed into the target coproduct
and then mapped by the target canonical isomorphism. -/
@[reassoc]
theorem normalizedChainComplexCoproductIso_hom_naturality_of_mono :
    (X.normalizedChainComplexCoproductIso R n).hom ≫ (normalizedChainComplexMap f R).f n =
      (sigmaConst.obj R).map (TypeCat.ofHom (nonDegenerateEmbeddingOfMono f n)) ≫
        (Y.normalizedChainComplexCoproductIso R n).hom := by
  apply Sigma.hom_ext
  intro x
  calc
    Sigma.ι (fun _ : X.nonDegenerate n => R) x ≫
        (X.normalizedChainComplexCoproductIso R n).hom ≫
          (normalizedChainComplexMap f R).f n
      = (Sigma.ι (fun _ : X.nonDegenerate n => R) x ≫
          (X.normalizedChainComplexCoproductIso R n).hom) ≫
            (normalizedChainComplexMap f R).f n := by
        rw [← Category.assoc]
    _ = X.ιNormalizedChainComplex (R := R) x.val ≫
          (normalizedChainComplexMap f R).f n := by
        rw [ι_normalizedChainComplexCoproductIso_hom]
    _ = Y.ιNormalizedChainComplex (R := R) (f.app _ x.val) := by
        rw [ι_normalizedChainComplexMap_f]
    _ = Y.ιNormalizedChainComplex (R := R)
          (nonDegenerateEmbeddingOfMono f n x).val := by
        rw [nonDegenerateEmbeddingOfMono_apply]
    _ = Sigma.ι (fun _ : Y.nonDegenerate n => R)
          (nonDegenerateEmbeddingOfMono f n x) ≫
            (Y.normalizedChainComplexCoproductIso R n).hom := by
        rw [← ι_normalizedChainComplexCoproductIso_hom]
    _ = (𝟙 R ≫ Sigma.ι (fun _ : Y.nonDegenerate n => R)
          (nonDegenerateEmbeddingOfMono f n x)) ≫
            (Y.normalizedChainComplexCoproductIso R n).hom := by
        rw [Category.id_comp]
    _ = (Sigma.ι (fun _ : X.nonDegenerate n => R) x ≫
          Sigma.map' (nonDegenerateEmbeddingOfMono f n)
            (fun _ => 𝟙 R)) ≫
              (Y.normalizedChainComplexCoproductIso R n).hom := by
        rw [Sigma.ι_comp_map']
    _ = Sigma.ι (fun _ : X.nonDegenerate n => R) x ≫
          (Sigma.map' (nonDegenerateEmbeddingOfMono f n)
            (fun _ => 𝟙 R) ≫
              (Y.normalizedChainComplexCoproductIso R n).hom) := by
        rw [Category.assoc]
    _ = Sigma.ι (fun _ : X.nonDegenerate n => R) x ≫
          ((sigmaConst.obj R).map
            (TypeCat.ofHom (nonDegenerateEmbeddingOfMono f n)) ≫
              (Y.normalizedChainComplexCoproductIso R n).hom) := by
        dsimp [sigmaConst]

end SSet
