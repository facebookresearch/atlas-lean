/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.TotalComplexDownNat
public import MathlibExt.Algebra.Homology.Embedding.StupidTruncInclusion
public import MathlibExt.Algebra.Homology.InitialSegmentShape

import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# First-coordinate partial total complexes

Truncating the first coordinate of a nonnegative bicomplex at p and
totalizing gives its pth partial total. The stupid-truncation inclusion
induces a monomorphism from this stage to the full total complex.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

/-- The initial-segment embedding preserves the retained natural degree. -/
private theorem initialSegmentEmbedding_f (p : ℕ) (i : Fin (p + 1)) :
    (ComplexShape.embeddingDownNatInitialSegment p).f i = i.1 := rfl

section PartialTotal

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Stupid truncation of the first coordinate of a natural first-quadrant
bicomplex through degree `p`. -/
noncomputable def firstStupidTrunc (p : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  B.stupidTrunc (ComplexShape.embeddingDownNatInitialSegment p)

/-- The partial total through first-coordinate degree `p`. -/
noncomputable def partialTotal (p : ℕ) : ChainComplex C ℕ :=
  (B.firstStupidTrunc p).total (ComplexShape.down ℕ)

/-- The canonical inclusion of the partial total into the full total complex. -/
noncomputable def partialTotalι (p : ℕ) :
    B.partialTotal p ⟶ B.total (ComplexShape.down ℕ) :=
  total.map
    (B.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment p))
    (ComplexShape.down ℕ)

/-- On a retained bicomplex summand, the partial-total inclusion is the
stupid-truncation component isomorphism followed by the full-total inclusion. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalι (p : ℕ) (i : Fin (p + 1))
    (j n : ℕ) (h : i.1 + j = n) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i.1 j n h ≫
        (B.partialTotalι p).f n =
      ((B.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment p)
        (show (ComplexShape.embeddingDownNatInitialSegment p).f i = i.1
          from by
            dsimp only [ComplexShape.embeddingDownNatInitialSegment,
              ComplexShape.Embedding.mk'])).hom.f j) ≫
        B.ιTotal (ComplexShape.down ℕ) i.1 j n h := by
  change
    HomologicalComplex₂.ιTotal
          (B.stupidTrunc (ComplexShape.embeddingDownNatInitialSegment p))
          (ComplexShape.down ℕ) i.1 j n h ≫
        (total.map
          (B.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment p))
          (ComplexShape.down ℕ)).f n = _
  rw [ιTotal_map, HomologicalComplex.ιStupidTrunc_f B
    (ComplexShape.embeddingDownNatInitialSegment p) i.1]
  have hComponent :
      B.ιStupidTruncf (ComplexShape.embeddingDownNatInitialSegment p) i.1 =
        (B.stupidTruncXIso (ComplexShape.embeddingDownNatInitialSegment p)
          (HomologicalComplex₂.initialSegmentEmbedding_f p i)).hom := by
    simpa only [HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso,
      Iso.trans_hom] using
      (HomologicalComplex.ιStupidTruncf'_eq B
        (ComplexShape.embeddingDownNatInitialSegment p)
          (HomologicalComplex₂.initialSegmentEmbedding_f p i))
  exact congrArg (fun φ => φ.f j ≫ B.ιTotal (ComplexShape.down ℕ) i.1 j n h) hComponent

/-- Each degree of the partial-total inclusion is a monomorphism. -/
instance partialTotalι_f_mono (p n : ℕ) : Mono ((B.partialTotalι p).f n) := by
  let e := ComplexShape.embeddingDownNatInitialSegment p
  let φ := B.ιStupidTrunc e
  let π := ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)
  let X := HomologicalComplex₂.toGradedObject (B.stupidTrunc e)
  let Y := B.toGradedObject
  let θ := HomologicalComplex₂.toGradedObjectMap φ
  let hBX : HasBiproduct (X.mapObjFun π n) :=
    HasBiproduct.of_hasCoproduct _
  let hBY : HasBiproduct (Y.mapObjFun π n) :=
    HasBiproduct.of_hasCoproduct _
  let hMono : ∀ x : π ⁻¹' {n}, Mono (θ x.1) := fun x => by
      rcases x.1 with ⟨i, j⟩
      change Mono ((φ.f i).f j)
      by_cases hi : ∃ a, e.f a = i
      · obtain ⟨a, ha⟩ := hi
        let : IsIso (φ.f i) := HomologicalComplex.isIso_ιStupidTrunc_f B e ha
        change Mono ((HomologicalComplex.eval C (ComplexShape.down ℕ) j).map (φ.f i))
        infer_instance
      · have hzero := B.isZero_stupidTrunc_X e i (by simpa using hi)
        exact ((HomologicalComplex.eval C
          (ComplexShape.down ℕ) j).map_isZero hzero).mono ((φ.f i).f j)
  have hmap :
      GradedObject.mapMap θ π n =
        Limits.Sigma.map (fun x : π ⁻¹' {n} => θ x.1) := by
    apply GradedObject.mapObj_ext
    intro i hi
    rw [GradedObject.ι_mapMap]
    change
      θ i ≫ Limits.Sigma.ι (Y.mapObjFun π n) ⟨i, hi⟩ =
        Limits.Sigma.ι (X.mapObjFun π n) ⟨i, hi⟩ ≫
          Limits.Sigma.map (fun x : π ⁻¹' {n} => θ x.1)
    rw [Limits.Sigma.ι_map]
  change Mono (GradedObject.mapMap θ π n)
  rw [hmap]
  exact @Limits.Sigma.map_mono (π ⁻¹' {n}) C _ _
    (X.mapObjFun π n) (Y.mapObjFun π n) hBX hBY
    (fun x => θ x.1) hMono

/-- The partial-total inclusion is a monomorphism of chain complexes. -/
instance partialTotalι_mono (p : ℕ) : Mono (B.partialTotalι p) :=
  HomologicalComplex.mono_of_mono_f _ fun n => B.partialTotalι_f_mono p n

end PartialTotal

end HomologicalComplex₂

end
