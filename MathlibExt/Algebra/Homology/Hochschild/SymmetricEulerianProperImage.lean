/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianProperNormalization
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianHodge

/-!
# Proper shuffle quotients as zero-plus-first Eulerian images

Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an
A-module with compatible ground action. On the raw coefficient complex C,
put P = e^(0)+e^(1), and let P_N be its normalized counterpart on
N_n = M ⊗[k] (A/(k·1))^⊗n. The proper both-positive shuffle relation
modules are the kernels of these projectors.

The quotient sections [x] ↦ P(x) identify the proper raw quotient with
Im(P), and the normalized quotient with Im(P_N), as A-linear chain
complexes. The inverse maps include an image element and take its
quotient class. Both Eulerian weights zero and one are retained,
including the coefficient term in degree zero.

Normalization intertwines the quotient sections and gives a homotopy
equivalence Im(P) ≃ Im(P_N), obtained by restricting and projecting
the normalization maps and homotopies. The carrier height is max(u,v,w)
for the independent worlds of k, A and M.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A
and a compatible A-module M, the full first raw Eulerian projector
P = e_C^(0)+e_C^(1) satisfies P ∘ P = P as an A-linear chain map
on the raw coefficient Hochschild complex. -/
theorem algebraFirstEulerianChainMap_idempotent :
    algebraFirstEulerianChainMap k A M ≫ algebraFirstEulerianChainMap k A M =
      algebraFirstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, algebraFirstEulerianChainMap_f]
  exact algebraFirstEulerianOperator_idempotent k A M n

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the full first normalized Eulerian projector
P_N = e_N^(0)+e_N^(1) satisfies P_N ∘ P_N = P_N on the normalized
A-linear coefficient complex. -/
theorem algebraNormalizedFirstEulerianChainMap_idempotent :
    algebraNormalizedFirstEulerianChainMap k A M ≫ algebraNormalizedFirstEulerianChainMap k A M =
      algebraNormalizedFirstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, algebraNormalizedFirstEulerianChainMap_f]
  exact algebraNormalizedFirstEulerianOperator_idempotent k A M n

/-- For a commutative ℚ-algebra k, a commutative k-algebra A
and a compatible A-module M, the full first raw image complex is
Im(e_C^(0)+e_C^(1)) in A-module chain complexes.
It retains weight zero together with weight one. -/
def algebraFirstEulerianImageComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  image (algebraFirstEulerianChainMap k A M)

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the full first normalized image is
Im(e_N^(0)+e_N^(1)) on the complex
N_n = M ⊗[k] (A/(k·1))^⊗n, with its coefficient A-action. -/
def algebraNormalizedFirstEulerianImageComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  image (algebraNormalizedFirstEulerianChainMap k A M)

/-- For a commutative ℚ-algebra k, a commutative k-algebra A
and a compatible A-module M, let C_+ be the raw quotient by the
proper both-positive shuffle relations, which equal ker(P) for
P = e_C^(0)+e_C^(1). There is an A-linear chain isomorphism
C_+ ≅ Im(P), with forward value [x] ↦ P(x) and inverse value
y ↦ [y]. -/
def algebraFirstEulerianQuotientIso :
    algebraPositiveQuotientComplex k A M ≅ algebraFirstEulerianImageComplex k A M where
  hom := algebraPositiveEulerianSection k A M ≫ factorThruImage (algebraFirstEulerianChainMap k A M)
  inv := image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawPositiveProjection k A M
  hom_inv_id := by
    change (algebraPositiveEulerianSection k A M ≫
        factorThruImage (algebraFirstEulerianChainMap k A M)) ≫
      (image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawPositiveProjection k A M) =
        𝟙 (algebraPositiveQuotientComplex k A M)
    calc
      _ = algebraPositiveEulerianSection k A M ≫ algebraFirstEulerianChainMap k A M ≫
          algebraRawPositiveProjection k A M := by simp only [Category.assoc, image.fac_assoc]
      _ = (algebraPositiveEulerianSection k A M ≫ algebraRawPositiveProjection k A M) ≫
          (algebraPositiveEulerianSection k A M ≫ algebraRawPositiveProjection k A M) := by
        rw [← algebraRawPositiveProjection_eulerianSection]
        simp only [Category.assoc]
      _ = 𝟙 _ := by rw [algebraPositiveEulerianSection_projection, Category.id_comp]
  inv_hom_id := by
    change (image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawPositiveProjection k A M) ≫
      (algebraPositiveEulerianSection k A M ≫ factorThruImage (algebraFirstEulerianChainMap k A M)) =
        𝟙 (image (algebraFirstEulerianChainMap k A M))
    have hi := image_ι_factorThruImage_of_idempotent (algebraFirstEulerianChainMap k A M)
      (algebraFirstEulerianChainMap_idempotent k A M)
    calc
      _ = image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraFirstEulerianChainMap k A M ≫
          factorThruImage (algebraFirstEulerianChainMap k A M) := by
        rw [Category.assoc, ← Category.assoc (algebraRawPositiveProjection k A M),
          algebraRawPositiveProjection_eulerianSection]
      _ = (image.ι (algebraFirstEulerianChainMap k A M) ≫
          factorThruImage (algebraFirstEulerianChainMap k A M)) ≫
            (image.ι (algebraFirstEulerianChainMap k A M) ≫
              factorThruImage (algebraFirstEulerianChainMap k A M)) := by
        have h := congrArg
          (fun t : algebraRawComplex k A M ⟶ algebraRawComplex k A M =>
            image.ι (algebraFirstEulerianChainMap k A M) ≫ t ≫
              factorThruImage (algebraFirstEulerianChainMap k A M))
          (image.fac (algebraFirstEulerianChainMap k A M)).symm
        simp only [Category.assoc] at h ⊢
        exact h
      _ = 𝟙 _ := by rw [hi, Category.id_comp]

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the normalized proper relation quotient
N_+ is isomorphic as an A-linear chain complex to Im(P_N), where
P_N = e_N^(0)+e_N^(1). The forward map sends [x] to P_N(x),
and the inverse takes the quotient class of an image element. -/
def algebraNormalizedFirstEulerianQuotientIso :
    algebraNormalizedPositiveQuotientComplex k A M ≅ algebraNormalizedFirstEulerianImageComplex k A M where
  hom := algebraNormalizedPositiveEulerianSection k A M ≫
    factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)
  inv := image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫ algebraNormalizedPositiveProjection k A M
  hom_inv_id := by
    change (algebraNormalizedPositiveEulerianSection k A M ≫
        factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)) ≫
      (image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
        algebraNormalizedPositiveProjection k A M) =
          𝟙 (algebraNormalizedPositiveQuotientComplex k A M)
    calc
      _ = algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizedFirstEulerianChainMap k A M ≫
          algebraNormalizedPositiveProjection k A M := by simp only [Category.assoc, image.fac_assoc]
      _ = (algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizedPositiveProjection k A M) ≫
          (algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizedPositiveProjection k A M) := by
        rw [← algebraNormalizedPositiveProjection_eulerianSection]
        simp only [Category.assoc]
      _ = 𝟙 _ := by rw [algebraNormalizedPositiveEulerianSection_projection, Category.id_comp]
  inv_hom_id := by
    change (image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
        algebraNormalizedPositiveProjection k A M) ≫
      (algebraNormalizedPositiveEulerianSection k A M ≫
        factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)) =
          𝟙 (image (algebraNormalizedFirstEulerianChainMap k A M))
    have hi := image_ι_factorThruImage_of_idempotent (algebraNormalizedFirstEulerianChainMap k A M)
      (algebraNormalizedFirstEulerianChainMap_idempotent k A M)
    calc
      _ = image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
          algebraNormalizedFirstEulerianChainMap k A M ≫
            factorThruImage (algebraNormalizedFirstEulerianChainMap k A M) := by
        rw [Category.assoc, ← Category.assoc (algebraNormalizedPositiveProjection k A M),
          algebraNormalizedPositiveProjection_eulerianSection]
      _ = (image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
          factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)) ≫
            (image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
              factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)) := by
        have h := congrArg
          (fun t : algebraNormalizedChainComplex k A M ⟶ algebraNormalizedChainComplex k A M =>
            image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫ t ≫
              factorThruImage (algebraNormalizedFirstEulerianChainMap k A M))
          (image.fac (algebraNormalizedFirstEulerianChainMap k A M)).symm
        simp only [Category.assoc] at h ⊢
        exact h
      _ = 𝟙 _ := by rw [hi, Category.id_comp]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A
and a compatible A-module M, the forward map C_+ → Im(P) is
C_+ → C → Im(P): first the section [x] ↦ P(x), then the
factorization of the raw first Eulerian projector P = e^(0)+e^(1). -/
theorem algebraFirstEulerianQuotientIso_hom :
    (algebraFirstEulerianQuotientIso k A M).hom =
      algebraPositiveEulerianSection k A M ≫ factorThruImage (algebraFirstEulerianChainMap k A M) := rfl

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the inverse Im(P) → C_+ is the raw
image inclusion followed by the proper quotient projection.
Thus an image element y is sent to its class [y]. -/
theorem algebraFirstEulerianQuotientIso_inv :
    (algebraFirstEulerianQuotientIso k A M).inv =
      image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawPositiveProjection k A M := rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
a compatible A-module M, let q : C → N be normalization and
q_+ : C_+ → N_+ its proper-quotient map. The sections satisfy
q ∘ s_C = s_N ∘ q_+ from the raw proper quotient to N,
where s_C([x]) = P(x) and s_N([y]) = P_N(y). -/
@[reassoc]
theorem algebraPositiveEulerianSection_normalization :
    algebraPositiveEulerianSection k A M ≫ algebraNormalizationProjection k A M =
      algebraPositiveNormalization k A M ≫ algebraNormalizedPositiveEulerianSection k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext y
  refine Quotient.inductionOn' y ?_
  intro x
  exact DFunLike.congr_fun (algebraNormalizationLevelMap_firstEulerian k A M n) x

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, normalization induces the A-linear chain
homotopy equivalence Im(e_C^(0)+e_C^(1)) ≃
Im(e_N^(0)+e_N^(1)). Its inverse and homotopies are the restricted
and projected normalization section and homotopies. -/
def algebraFirstEulerianImageNormalizationHomotopyEquiv :
    HomotopyEquiv (algebraFirstEulerianImageComplex k A M)
      (algebraNormalizedFirstEulerianImageComplex k A M) :=
  HomologicalComplex.homotopyEquivOnSplitImages
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraNormalizationHomotopyEquiv k A M).homotopyHomInvId
    (image.ι (algebraFirstEulerianChainMap k A M)) (factorThruImage (algebraFirstEulerianChainMap k A M))
    (image_ι_factorThruImage_of_idempotent _ (algebraFirstEulerianChainMap_idempotent k A M))
    (image.ι (algebraNormalizedFirstEulerianChainMap k A M))
    (factorThruImage (algebraNormalizedFirstEulerianChainMap k A M))
    (image_ι_factorThruImage_of_idempotent _ (algebraNormalizedFirstEulerianChainMap_idempotent k A M))
    (by
      change (factorThruImage (algebraFirstEulerianChainMap k A M) ≫
          image.ι (algebraFirstEulerianChainMap k A M)) ≫ algebraNormalizationProjection k A M =
        algebraNormalizationProjection k A M ≫
          (factorThruImage (algebraNormalizedFirstEulerianChainMap k A M) ≫
            image.ι (algebraNormalizedFirstEulerianChainMap k A M))
      exact (congrArg (fun t => t ≫ algebraNormalizationProjection k A M)
        (image.fac (algebraFirstEulerianChainMap k A M))).trans
        ((algebraNormalizationProjection_firstEulerian k A M).symm.trans
          (congrArg (fun t => algebraNormalizationProjection k A M ≫ t)
            (image.fac (algebraNormalizedFirstEulerianChainMap k A M)).symm)))

end ModuleCat.Algebra.Hochschild.Symmetric
