/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.CoefficientIdealCountFaces

/-!
# Ideal-count filtrations for positive coefficient bar words

The bar b′ boundary in whole-word coordinates is the alternating sum of the non-wrapping
adjacent faces, with signs (−1)^i. Tensoring it with identity on an arbitrary coefficient V
gives the coefficient word boundary.

Under the positive bar word isomorphisms, this is the differential from word length n + 2 in
degree n + 2 to length n + 1 in degree n + 1. The relative quotient-kernel word maps commute
with it, and the degree-zero relative object is zero. Because each face loses at most one
ideal entry, every stage requiring n + 1 − p ideal entries is preserved.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]
  (V : Type w) [AddCommGroup V] [Module k V]

/-- Let k be commutative and A a nonunital k-algebra ring with k-bilinear multiplication.
regularWordTruncatedBoundary n : A^⊗(n+2) →ₗ[k] A^⊗(n+1) is the bPrimeComplex boundary
transported by TensorPower.consEquiv. -/
def regularWordTruncatedBoundary (n : ℕ) :
    TensorPower k (n + 2) A →ₗ[k] TensorPower k (n + 1) A :=
  (TensorPower.consEquiv k A n).toLinearMap.comp
    (((bPrimeComplex k A).d (n + 1) n).hom.comp
      (TensorPower.consEquiv k A (n + 1)).symm.toLinearMap)

/-- For a nonunital k-algebra ring A over commutative k, regularWordTruncatedBoundary n = ∑ i :
Fin(n+1), (−1 : ℤ)^i.val • regularWordFace n i.castSucc. Thus only the n + 1 adjacent
non-wrapping faces occur. -/
theorem regularWordTruncatedBoundary_eq_sum (n : ℕ) :
    regularWordTruncatedBoundary k A n =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • regularWordFace k A n i.castSucc := by
  apply LinearMap.ext
  intro x
  have h := congrArg
    (fun f : chainLevel k A A (n + 1) ⟶ chainLevel k A A n =>
      TensorPower.consEquiv k A n
        (f.hom ((TensorPower.consEquiv k A (n + 1)).symm x)))
    (bPrimeComplex_d k A n)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul] at h
  change TensorPower.consEquiv k A n
      (((bPrimeComplex k A).d (n + 1) n).hom
        ((TensorPower.consEquiv k A (n + 1)).symm x)) =
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • regularWordFace k A n i.castSucc) x
  rw [LinearMap.sum_apply]
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact (map_zsmul
    (LinearMap.applyₗ (R := k) (M := TensorPower k (n + 2) A)
      (M₂ := TensorPower k (n + 1) A) x)
    ((-1 : ℤ) ^ i.val) (regularWordFace k A n i.castSucc)).symm

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V an arbitrary k-module.
Write K_+ for the relative positive bar quotient kernel, whose degree n + 1 has a word map
W_n^V into V ⊗[k] A^⊗(n+1). coefficientWordBoundary n is id_V ⊗ regularWordTruncatedBoundary
n, mapping V ⊗ A^⊗(n+2) to V ⊗ A^⊗(n+1). -/
def coefficientWordBoundary (n : ℕ) :
    V ⊗[k] TensorPower k (n + 2) A →ₗ[k] V ⊗[k] TensorPower k (n + 1) A :=
  TensorProduct.map (LinearMap.id : V →ₗ[k] V) (regularWordTruncatedBoundary k A n)

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V an arbitrary k-module.
Write K_+ for the relative positive bar quotient kernel, whose degree n + 1 has a word map
W_n^V into V ⊗[k] A^⊗(n+1). coefficientWordBoundary n = ∑ i : Fin(n+1), (−1 : ℤ)^i.val • (id_V
⊗ regularWordFace n i.castSucc). -/
theorem coefficientWordBoundary_eq_sum (n : ℕ) :
    coefficientWordBoundary k A V n =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        TensorProduct.map (LinearMap.id : V →ₗ[k] V) (regularWordFace k A n i.castSucc) := by
  classical
  apply TensorProduct.ext'
  intro v x
  simp only [coefficientWordBoundary, TensorProduct.map_tmul, LinearMap.id_apply,
    regularWordTruncatedBoundary_eq_sum, LinearMap.sum_apply, LinearMap.smul_apply]
  change (TensorProduct.mk k V (TensorPower k (n + 1) A) v)
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • regularWordFace k A n i.castSucc x) = _
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V an arbitrary k-module.
Write K_+ for the relative positive bar quotient kernel, whose degree n + 1 has a word map
W_n^V into V ⊗[k] A^⊗(n+1). For n,r : ℕ, coefficientIdealWordSpan (n + 2) r mapped by
coefficientWordBoundary n is contained in coefficientIdealWordSpan (n + 1) (r−1). -/
theorem coefficientIdealWordSpan_boundary (n required : ℕ) :
    (coefficientIdealWordSpan k A I V (n + 2) required).map
        (coefficientWordBoundary k A V n) ≤
      coefficientIdealWordSpan k A I V (n + 1) (required - 1) := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  change coefficientWordBoundary k A V n x ∈
    coefficientIdealWordSpan k A I V (n + 1) (required - 1)
  rw [coefficientWordBoundary_eq_sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  have heval : (((-1 : ℤ) ^ i.val) •
      TensorProduct.map (LinearMap.id : V →ₗ[k] V) (regularWordFace k A n i.castSucc)) x =
      ((-1 : ℤ) ^ i.val) •
        TensorProduct.map (LinearMap.id : V →ₗ[k] V) (regularWordFace k A n i.castSucc) x :=
    map_zsmul
      (LinearMap.applyₗ (R := k) (M := V ⊗[k] TensorPower k (n + 2) A)
        (M₂ := V ⊗[k] TensorPower k (n + 1) A) x)
      ((-1 : ℤ) ^ i.val)
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V) (regularWordFace k A n i.castSucc))
  rw [heval]
  exact (coefficientIdealWordSpan k A I V (n + 1) (required - 1)).toAddSubgroup.zsmul_mem
    ((Submodule.map_le_iff_le_comap.mp
      (coefficientIdealWordSpan_regularWordFace k A I V n required i)) hx) ((-1 : ℤ) ^ i.val)

private abbrev barWordCoordinates (n : ℕ) :
    V ⊗[k] (A ⊗[k] TensorPower k n A) ≃ₗ[k] V ⊗[k] TensorPower k (n + 1) A :=
  TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)

omit [IsScalarTower k A A] [SMulCommClass k A A] in
private theorem barWordCoordinates_tmul (n : ℕ) (v : V) (x : A ⊗[k] TensorPower k n A) :
    barWordCoordinates k A V n (v ⊗ₜ[k] x) = v ⊗ₜ[k] TensorPower.consEquiv k A n x :=
  TensorProduct.congr_tmul _ _ _ _

private theorem barWordCoordinates_d (n : ℕ) :
    (barComplex k A V).d (n + 1) n ≫ (barWordCoordinates k A V n).toModuleIso.hom =
      (barWordCoordinates k A V (n + 1)).toModuleIso.hom ≫
        ModuleCat.ofHom (coefficientWordBoundary k A V n) := by
  let d : (A ⊗[k] TensorPower k (n + 1) A) →ₗ[k] (A ⊗[k] TensorPower k n A) :=
    ((bPrimeComplex k A).d (n + 1) n).hom
  apply ModuleCat.hom_ext
  change (barWordCoordinates k A V n).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V) d) =
    (coefficientWordBoundary k A V n).comp (barWordCoordinates k A V (n + 1)).toLinearMap
  apply TensorProduct.ext' (M := V) (N := A ⊗[k] TensorPower k (n + 1) A)
  intro v x
  change barWordCoordinates k A V n
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V) d (v ⊗ₜ[k] x)) =
    coefficientWordBoundary k A V n (barWordCoordinates k A V (n + 1) (v ⊗ₜ[k] x))
  rw [TensorProduct.map_tmul, LinearMap.id_apply, barWordCoordinates_tmul,
    barWordCoordinates_tmul]
  rw [coefficientWordBoundary, TensorProduct.map_tmul, LinearMap.id_apply]
  change v ⊗ₜ[k] TensorPower.consEquiv k A n
      (d x) =
    v ⊗ₜ[k] TensorPower.consEquiv k A n
      (d
        ((TensorPower.consEquiv k A (n + 1)).symm
          (TensorPower.consEquiv k A (n + 1) x)))
  rw [LinearEquiv.symm_apply_apply]

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V an arbitrary k-module.
Write K_+ for the relative positive bar quotient kernel, whose degree n + 1 has a word map
W_n^V into V ⊗[k] A^⊗(n+1). For n : ℕ, d_positive(n+2,n+1) ≫ positiveBarWordIso n.hom =
positiveBarWordIso (n+1).hom ≫ ModuleCat.ofHom (coefficientWordBoundary n). -/
theorem positiveBarWordIso_d (n : ℕ) :
    (positiveBarComplex k A V).d (n + 2) (n + 1) ≫ (positiveBarWordIso k A V n).hom =
      (positiveBarWordIso k A V (n + 1)).hom ≫
        ModuleCat.ofHom (coefficientWordBoundary k A V n) := by
  let e : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 1
  have hsource : e.f (n + 1) = n + 2 := rfl
  have htarget : e.f n = n + 1 := rfl
  let es : ((barComplex k A V).extend e).X (n + 2) ≅ (barComplex k A V).X (n + 1) :=
    (barComplex k A V).extendXIso e hsource
  let et : ((barComplex k A V).extend e).X (n + 1) ≅ (barComplex k A V).X n :=
    (barComplex k A V).extendXIso e htarget
  let cs : (barComplex k A V).X (n + 1) ≅
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 2) A) :=
    (barWordCoordinates k A V (n + 1)).toModuleIso
  let ct : (barComplex k A V).X n ≅
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A) :=
    (barWordCoordinates k A V n).toModuleIso
  have hext : ((barComplex k A V).extend e).d (n + 2) (n + 1) =
      es.hom ≫ (barComplex k A V).d (n + 1) n ≫ et.inv :=
    (barComplex k A V).extend_d_eq e hsource htarget
  have hcoords : (barComplex k A V).d (n + 1) n ≫ ct.hom =
      cs.hom ≫ ModuleCat.ofHom (coefficientWordBoundary k A V n) :=
    barWordCoordinates_d k A V n
  change ((barComplex k A V).extend e).d (n + 2) (n + 1) ≫
      (et.hom ≫ ct.hom) =
    (es.hom ≫ cs.hom) ≫ ModuleCat.ofHom (coefficientWordBoundary k A V n)
  rw [hext]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hcoords]

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V an arbitrary k-module.
Write K_+ for the relative positive bar quotient kernel, whose degree n + 1 has a word map
W_n^V into V ⊗[k] A^⊗(n+1). For x : K_+.X (n + 2), W_n^V(K_+.d (n+2)(n+1) x) =
coefficientWordBoundary n (W_(n+1)^V(x)). -/
theorem relativePositiveBarWordMap_d (n : ℕ)
    (x : (relativePositiveBarComplex k A I V).X (n + 2)) :
    relativePositiveBarWordMap k A I V n
        (((relativePositiveBarComplex k A I V).d (n + 2) (n + 1)).hom x) =
      coefficientWordBoundary k A V n (relativePositiveBarWordMap k A I V (n + 1) x) := by
  have hcomm := (kernel.ι (positiveBarQuotientMap k A I V)).comm (n + 2) (n + 1)
  have hsquare := congrArg
    (fun f : (relativePositiveBarComplex k A I V).X (n + 2) ⟶
      (positiveBarComplex k A V).X (n + 1) => f ≫ (positiveBarWordIso k A V n).hom) hcomm
  simp only [Category.assoc, positiveBarWordIso_d] at hsquare
  have hvalue := congrArg
    (fun f : (relativePositiveBarComplex k A I V).X (n + 2) ⟶
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A) => f.hom x) hsquare
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hvalue
  exact hvalue.symm

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V an arbitrary k-module.
Write K_+ for the relative positive bar quotient kernel, whose degree n + 1 has a word map
W_n^V into V ⊗[k] A^⊗(n+1). The object K_+.X 0 is zero, since the positive bar source is zero
in degree zero and the relative object is its quotient-map kernel. -/
theorem relativePositiveBarComplex_isZero_zero :
    IsZero ((relativePositiveBarComplex k A I V).X 0) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← cancel_mono ((kernel.ι (positiveBarQuotientMap k A I V)).f 0)]
  exact (positiveBarComplex_isZero_zero k A V).eq_of_tgt _ _

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V an arbitrary k-module.
Write K_+ for the relative positive bar quotient kernel, whose degree n + 1 has a word map
W_n^V into V ⊗[k] A^⊗(n+1). For p,n : ℕ, the image of barWordFiltration p (n + 1) under K_+.d
(n + 2) (n + 1) lies in barWordFiltration p n. These stages are in positive degrees n + 2 and
n + 1, respectively. -/
theorem barWordFiltration_d (p n : ℕ) :
    (barWordFiltration k A I V p (n + 1)).map
        ((relativePositiveBarComplex k A I V).d (n + 2) (n + 1)).hom ≤
      barWordFiltration k A I V p n := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  change relativePositiveBarWordMap k A I V (n + 1) x ∈
    coefficientIdealWordSpan k A I V (n + 2) (n + 2 - p) at hx
  change relativePositiveBarWordMap k A I V n
      (((relativePositiveBarComplex k A I V).d (n + 2) (n + 1)).hom x) ∈
    coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p)
  rw [relativePositiveBarWordMap_d]
  have h := (Submodule.map_le_iff_le_comap.mp
    (coefficientIdealWordSpan_boundary k A I V n (n + 2 - p))) hx
  change coefficientWordBoundary k A V n (relativePositiveBarWordMap k A I V (n + 1) x) ∈
    coefficientIdealWordSpan k A I V (n + 1) (n + 2 - p - 1) at h
  have hthreshold : n + 2 - p - 1 = n + 1 - p := by omega
  simpa only [hthreshold] using h

end ModuleCat.Algebra.Hochschild.NonUnital
