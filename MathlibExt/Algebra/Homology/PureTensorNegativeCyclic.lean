/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

/-!
# Actual pure-coefficient tensors and weighted negative-cyclic comparison

A pure weight-zero coefficient complex C tensors each actual mixed
weight with C. Its mixed differential acts on the first factor, with
every homogeneous tensor generator fixed. The NC comparison sends
every complete product coefficient through the native cochain tensor
summand, including all i≥0 closing coefficients.

Perfection of C makes this comparison a quasi-isomorphism through a
separate proof request. The comparison model itself assumes neither
perfection nor invertibility. Reference: PTVV arXiv:1111.3209v4,
§2.1, pp.31--32.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.PureTensorNegativeCyclic

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open CochainComplex.HomComplex

universe u
variable {R : Type u} [CommRing R]

/-- A pure coefficient tensor keeps every actual weight and mixed cochain component. -/
structure PureTensorModel (E : GradedMixed R) (C : CochainComplex (ModuleCat.{u} R) ℤ) where
  mixed : GradedMixed R
  weightIso : ∀ w : ℤ, mixed.weight w ≅ E.weight w ⊗ C
  epsilon : ∀ (w p q n : ℤ) (h : p + q = n) (x : (E.weight w).X p) (c : C.X q),
    ((weightIso (w + 1)).hom.f (n - 1)).hom
      (((mixed.epsilon w).v n (n - 1) (by omega)).hom
        (((weightIso w).inv.f n).hom
          ((HomologicalComplex.ιTensorObj (E.weight w) C p q n h).hom
            (TensorProduct.tmul R x c)))) =
    (HomologicalComplex.ιTensorObj (E.weight (w + 1)) C (p - 1) q (n - 1) (by omega)).hom
      (TensorProduct.tmul R (((E.epsilon w).v p (p - 1) (by omega)).hom x) c)

/-- The canonical NC tensor comparison fixes every product closing coefficient. -/
structure Comparison {E : GradedMixed R} {C : CochainComplex (ModuleCat.{u} R) ℤ}
    (P : PureTensorModel E C) (p : ℤ) (M : NegativeCyclicModel E p)
    (N : NegativeCyclicModel P.mixed p) where
  map : M.complex ⊗ C ⟶ N.complex
  normalized : ∀ (a b n : ℤ) (h : a + b = n) (x : M.complex.X a) (c : C.X b) (i : ℕ),
    (N.termIso n).hom
      (((HomologicalComplex.ιTensorObj M.complex C a b n h) ≫ map.f n).hom
        (TensorProduct.tmul R x c)) i =
    (((P.weightIso (p + (i : ℤ))).inv.f (n - 2 * (i : ℤ))).hom
      ((HomologicalComplex.ιTensorObj (E.weight (p + (i : ℤ))) C
        (a - 2 * (i : ℤ)) b (n - 2 * (i : ℤ)) (by omega)).hom
          (TensorProduct.tmul R ((M.termIso a).hom x i) c)))

/-- The induced NC map is fixed by the actual mixed-map product formula. -/
structure CyclicMapModel {E F : GradedMixed R} (f : MixedMap E F) (p : ℤ)
    (M : NegativeCyclicModel E p) (N : NegativeCyclicModel F p) where
  map : M.complex ⟶ N.complex
  normalized : IsNegativeCyclicMap f p M N map

end MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
