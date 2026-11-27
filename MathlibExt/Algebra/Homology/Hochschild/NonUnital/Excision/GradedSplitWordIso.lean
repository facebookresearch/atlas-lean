/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.SplitWordFiltration
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationZeroImage
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveFiltrationZeroImage
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exact relative split-word grade coordinates

Let A → A/I be a ground-linear split quotient. In word length N = n + 1, form the finite
family Γ_p,n of colours with exactly p quotient positions. The relative coordinate submodule
R_p,n has its all-quotient coordinate zero, because the relative word lies in the kernel of
the tensor quotient.

Summing the colour inclusions reconstructs a tensor in that kernel and in filtration stage
F_p. Extracting exactly the p-count coordinates has predecessor F_(p−1) as kernel, with zero
predecessor at p = 0. These maps induce mutually inverse equivalences F_p/F_lower ≃ₗ[k] R_p,n,
for both the naive and arbitrary-coefficient positive bar layers.

When p < n + 1, the all-quotient colour is absent and R_p,n is the complete fixed-count
family. When n + 1 ≤ p, the relative family and layer are zero. The final isomorphisms
identify individual associated-complex terms; they do not specify a differential on the
coordinate family or an excision homology isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

section NativeKernelTransport

variable {k : Type u} [CommRing k]
  {ι : Type w} {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat.{z} k) c}

private def componentKernelEquiv (f : C ⟶ D) (i : ι) :
    (kernel f).X i ≃ₗ[k] LinearMap.ker (f.f i).hom :=
  ((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{z} k) c i) f) ≪≫
    ModuleCat.kernelIsoKer (f.f i)).toLinearEquiv

private theorem componentKernelEquiv_val (f : C ⟶ D) (i : ι)
    (x : (kernel f).X i) :
    (componentKernelEquiv f i x : C.X i) = ((kernel.ι f).f i).hom x := by
  have hcat :
      ((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{z} k) c i) f) ≪≫
          ModuleCat.kernelIsoKer (f.f i)).hom ≫
        ModuleCat.ofHom ((LinearMap.ker ((f.f i).hom)).subtype) = (kernel.ι f).f i := by
    simp only [Iso.trans_hom, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
      PreservesKernel.iso_hom]
    exact kernelComparison_comp_ι f (HomologicalComplex.eval (ModuleCat.{z} k) c i)
  have hx := congrArg
    (fun g : (kernel f).X i ⟶ C.X i => g.hom x) hcat
  have hmap : (componentKernelEquiv f i).toLinearMap =
      (((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{z} k) c i) f) ≪≫
        ModuleCat.kernelIsoKer (f.f i)).hom).hom :=
    CategoryTheory.Iso.toLinearMap_toLinearEquiv _
  have he : componentKernelEquiv f i x =
      (((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{z} k) c i) f) ≪≫
        ModuleCat.kernelIsoKer (f.f i)).hom).hom x := DFunLike.congr_fun hmap x
  apply (congrArg (fun y : LinearMap.ker (f.f i).hom => y.val) he).trans
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    Submodule.subtype_apply] using hx

variable {M Q W T : Type z} [AddCommGroup M] [Module k M]
  [AddCommGroup Q] [Module k Q] [AddCommGroup W] [Module k W]
  [AddCommGroup T] [Module k T]

private theorem kernelWordTransport_eq (f : M →ₗ[k] Q) (q : W →ₗ[k] T)
    (e : M ≃ₗ[k] W) (t : Q ≃ₗ[k] T)
    (h : t.toLinearMap.comp f = q.comp e.toLinearMap) :
    LinearMap.ker f = (LinearMap.ker q).comap e.toLinearMap := by
  apply Submodule.ext
  intro x
  change f x = 0 ↔ q (e x) = 0
  have hx := congrArg (fun g : M →ₗ[k] T => g x) h
  change t (f x) = q (e x) at hx
  rw [← hx]
  constructor
  · intro hf
    rw [hf, map_zero]
  · intro ht
    apply t.injective
    simpa only [map_zero] using ht

end NativeKernelTransport

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]
  (splitting : I.KSplit)

/-- Let k be commutative, A a nonunital k-module ring and I a k-subalgebra, with quotient-linear
map q : A → A/I. For N : ℕ, originalQuotientWordMap N : A^⊗N →ₗ[k] (A/I)^⊗N is
PiTensorProduct.map (fun _ => q). -/
def originalQuotientWordMap (N : ℕ) :
    TensorPower k N A →ₗ[k] TensorPower k N I.Quotient :=
  PiTensorProduct.map (fun _ : Fin N => NonUnitalSubalgebra.Quotient.mkL I)

private theorem naiveQuotient_word_natural (n : ℕ) :
    (TensorPower.consEquiv k I.Quotient n).toLinearMap.comp
        ((cyclicBComplexHom I.quotientMap).f n).hom =
      (originalQuotientWordMap k A I (n + 1)).comp
        (TensorPower.consEquiv k A n).toLinearMap := by
  rw [cyclicBComplexHom_f]
  exact TensorPower.consEquiv_naturality (NonUnitalSubalgebra.Quotient.mkL I) n

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Let q_N : A^⊗N → Q^⊗N be the tensor quotient, K_b,n the
relative naive kernel term and W_n its ambient word inclusion. relativeNaiveWordKernelEquiv n
: K_b,n ≃ₗ[k] ker q_N is obtained by kernel preservation under degree evaluation and the
first-factor tensor equivalences. -/
def relativeNaiveWordKernelEquiv (n : ℕ) :
    (relativeNaiveComplex k A I).X n ≃ₗ[k]
      LinearMap.ker (originalQuotientWordMap k A I (n + 1)) :=
  ((PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n)
      (cyclicBComplexHom I.quotientMap)) ≪≫
    ModuleCat.kernelIsoKer ((cyclicBComplexHom I.quotientMap).f n)).toLinearEquiv.trans
      ((LinearEquiv.ofEq _ _ (by
        exact kernelWordTransport_eq ((cyclicBComplexHom I.quotientMap).f n).hom
          (originalQuotientWordMap k A I (n + 1))
          (TensorPower.consEquiv k A n) (TensorPower.consEquiv k I.Quotient n)
          (naiveQuotient_word_natural k A I n))).trans
        ((TensorPower.consEquiv k A n).ofSubmodule'
          (LinearMap.ker (originalQuotientWordMap k A I (n + 1)))))

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Let q_N : A^⊗N → Q^⊗N be the tensor quotient, K_b,n the
relative naive kernel term and W_n its ambient word inclusion. For x : K_b,n, the underlying
ambient tensor of relativeNaiveWordKernelEquiv n x equals W_n(x). -/
theorem relativeNaiveWordKernelEquiv_val (n : ℕ)
    (x : (relativeNaiveComplex k A I).X n) :
    (relativeNaiveWordKernelEquiv k A I n x : TensorPower k (n + 1) A) =
      relativeNaiveWordMap k A I n x := by
  rw [relativeNaiveWordKernelEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.ofSubmodule'_apply, LinearEquiv.coe_ofEq_apply]
  change TensorPower.consEquiv k A n
      (componentKernelEquiv (cyclicBComplexHom I.quotientMap) n x : (bComplex k A).X n) =
    relativeNaiveWordMap k A I n x
  rw [componentKernelEquiv_val]
  rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and s a k-linear quotient section. Let K_b be the relative naive kernel and W_n its inclusion
in word coordinates of length n + 1. For x : K_b.X n and the all-true colour c,
splitAmbientToWord s c (W_n x) = 0, since this colour projection is the tensor quotient. -/
theorem relativeNaiveWord_allQuotient_zero (n : ℕ)
    (colour : Fin (n + 1) → Bool) (hc : colour = fun _ => true)
    (x : (relativeNaiveComplex k A I).X n) :
    splitAmbientToWord k A I splitting colour (relativeNaiveWordMap k A I n x) = 0 := by
  subst colour
  change originalQuotientWordMap k A I (n + 1) (relativeNaiveWordMap k A I n x) = 0
  rw [← relativeNaiveWordKernelEquiv_val k A I n x]
  exact (relativeNaiveWordKernelEquiv k A I n x).property

/-- Let k be commutative, A a nonunital k-module ring, I a k-subalgebra and N = n + 1. For a
colour c : Fin N → Bool, let W_c tensor I at false positions and A/I at true positions. In
Γ_p,n = Π c with exactly p true positions, W_c, naiveRelativeSplitWordGradeSpace is the
submodule of families whose all-true coordinate is zero. -/
def naiveRelativeSplitWordGradeSpace (p n : ℕ) :
    Submodule k (naiveSplitWordGradeCoordinates k A I p n) where
  carrier := {y | ∀ colour : splitWordGradeColours p (n + 1),
    colour.val = (fun _ => true) → y colour = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy colour hc := by
    change x colour + y colour = (0 : splitWordTensor k A I colour.val)
    rw [hx colour hc, hy colour hc, add_zero]
  smul_mem' r x hx colour hc := by
    change r • x colour = (0 : splitWordTensor k A I colour.val)
    rw [hx colour hc, smul_zero]

/-- Let k be commutative, A a nonunital k-module ring, I a k-subalgebra and N = n + 1. Let W_c
tensor I at false positions and A/I at true positions. naiveRelativeSplitWordGradeCoordinates
p n is the submodule of Π c with exactly p true positions, W_c imposing a zero all-true
coordinate. -/
abbrev naiveRelativeSplitWordGradeCoordinates (p n : ℕ) :=
  naiveRelativeSplitWordGradeSpace k A I p n

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and s a k-linear quotient
section. Put N = n + 1, let W_c tensor I at false and A/I at true positions, and let J_c
tensor the inclusion or section. naiveFixedGradeToAmbient maps Γ_p,n = Π c with p true
positions, W_c to A^⊗N by y ↦ ∑ c, J_c(y_c). -/
def naiveFixedGradeToAmbient (p n : ℕ) :
    naiveSplitWordGradeCoordinates k A I p n →ₗ[k] TensorPower k (n + 1) A :=
  ∑ colour : splitWordGradeColours p (n + 1),
    (splitWordToAmbient k A I splitting colour.val).comp (LinearMap.proj colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem naiveFixedGradeToAmbient_apply (p n : ℕ)
    (y : naiveSplitWordGradeCoordinates k A I p n) :
    naiveFixedGradeToAmbient k A I splitting p n y =
      ∑ colour : splitWordGradeColours p (n + 1),
        splitWordToAmbient k A I splitting colour.val (y colour) := by
  simp only [naiveFixedGradeToAmbient, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem naiveFixedGradeToAmbient_coordinate (p n : ℕ)
    (y : naiveSplitWordGradeCoordinates k A I p n)
    (target : splitWordGradeColours p (n + 1)) :
    splitAmbientToWord k A I splitting target.val
        (naiveFixedGradeToAmbient k A I splitting p n y) = y target := by
  classical
  rw [naiveFixedGradeToAmbient_apply, map_sum]
  have ht (source : splitWordGradeColours p (n + 1)) :
      splitAmbientToWord k A I splitting target.val
          (splitWordToAmbient k A I splitting source.val (y source)) =
        if source = target then y target else 0 := by
    by_cases h : source = target
    · subst source
      rw [ite_eq_left rfl]
      exact congrArg (fun f => f (y target))
        (splitAmbientToWord_comp_splitWordToAmbient k A I splitting target.val)
    · rw [ite_eq_right h]
      exact congrArg (fun f => f (y source))
        (splitAmbientToWord_comp_splitWordToAmbient_zero k A I splitting source.val target.val
          (fun hv => h (Subtype.ext hv)))
  simp_rw [ht]
  simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem naiveFixedGradeToAmbient_quotient_zero (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    originalQuotientWordMap k A I (n + 1)
      (naiveFixedGradeToAmbient k A I splitting p n y.val) = 0 := by
  classical
  rw [naiveFixedGradeToAmbient_apply, map_sum]
  apply Finset.sum_eq_zero
  intro colour _
  by_cases hc : colour.val = fun _ => true
  · rw [y.property colour hc, map_zero, map_zero]
  · change splitAmbientToWord k A I splitting (fun _ : Fin (n + 1) => true)
      (splitWordToAmbient k A I splitting colour.val (y.val colour)) = 0
    exact congrArg (fun f => f (y.val colour))
      (splitAmbientToWord_comp_splitWordToAmbient_zero k A I splitting colour.val
        (fun _ => true) hc)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem naiveFixedGradeToAmbient_mem_span (p n : ℕ)
    (y : naiveSplitWordGradeCoordinates k A I p n) :
    naiveFixedGradeToAmbient k A I splitting p n y ∈
      idealWordSpan k A I (n + 1) (n + 1 - p) := by
  classical
  rw [naiveFixedGradeToAmbient_apply]
  apply Submodule.sum_mem
  intro colour _
  have hc := splitWordPositionCounts_add colour.val
  have hq := colour.property
  have hrequired : n + 1 - p ≤ splitWordIdealPositionCount colour.val := by omega
  exact splitWordToAmbient_range_le_idealWordSpan k A I splitting colour.val (n + 1 - p)
    hrequired ⟨y colour, rfl⟩

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. Restricting naiveFixedGradeToAmbient to R_p,n gives naiveFixedGradeToKernel : R_p,n
→ₗ[k] ker q_N. Every non-all-true colour has an ideal factor, and the all-true coordinate is
zero. -/
def naiveFixedGradeToKernel (p n : ℕ) :
    naiveRelativeSplitWordGradeCoordinates k A I p n →ₗ[k]
      LinearMap.ker (originalQuotientWordMap k A I (n + 1)) :=
  ((naiveFixedGradeToAmbient k A I splitting p n).comp
    (naiveRelativeSplitWordGradeSpace k A I p n).subtype).codRestrict
      (LinearMap.ker (originalQuotientWordMap k A I (n + 1)))
      (by
        intro y
        exact naiveFixedGradeToAmbient_quotient_zero k A I splitting p n y)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. naiveFixedGradeToRelative : R_p,n →ₗ[k] K_b,n is reconstruction into ker q_N
followed by relativeNaiveWordKernelEquiv n.symm. -/
def naiveFixedGradeToRelative (p n : ℕ) :
    naiveRelativeSplitWordGradeCoordinates k A I p n →ₗ[k]
      (relativeNaiveComplex k A I).X n :=
  (relativeNaiveWordKernelEquiv k A I n).symm.toLinearMap.comp
    (naiveFixedGradeToKernel k A I splitting p n)

private theorem naiveFixedGradeToRelative_word (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    relativeNaiveWordMap k A I n (naiveFixedGradeToRelative k A I splitting p n y) =
      naiveFixedGradeToAmbient k A I splitting p n y.val := by
  have h := congrArg (fun z : LinearMap.ker (originalQuotientWordMap k A I (n + 1)) => z.val)
    ((relativeNaiveWordKernelEquiv k A I n).apply_symm_apply
      (naiveFixedGradeToKernel k A I splitting p n y))
  rw [relativeNaiveWordKernelEquiv_val] at h
  exact h

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. naiveFixedGradeToStage : R_p,n →ₗ[k] F_p,n is the reconstructed relative term
restricted to the stage requiring n + 1 − p ideal entries. -/
def naiveFixedGradeToStage (p n : ℕ) :
    naiveRelativeSplitWordGradeCoordinates k A I p n →ₗ[k] naiveWordFiltration k A I p n :=
  (naiveFixedGradeToRelative k A I splitting p n).codRestrict (naiveWordFiltration k A I p n)
    (fun y => by
      change relativeNaiveWordMap k A I n (naiveFixedGradeToRelative k A I splitting p n y) ∈
        idealWordSpan k A I (n + 1) (n + 1 - p)
      rw [naiveFixedGradeToRelative_word]
      exact naiveFixedGradeToAmbient_mem_span k A I splitting p n y.val)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. For y : R_p,n, W_n(naiveFixedGradeToStage y) = ∑ c with p true positions, J_c(y_c). -/
theorem naiveFixedGradeToStage_word (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    relativeNaiveWordMap k A I n ((naiveFixedGradeToStage k A I splitting p n y).val) =
      ∑ colour : splitWordGradeColours p (n + 1),
        splitWordToAmbient k A I splitting colour.val (y.val colour) := by
  exact (naiveFixedGradeToRelative_word k A I splitting p n y).trans
    (naiveFixedGradeToAmbient_apply k A I splitting p n y.val)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. naiveStageToRelativeFixedGrade maps F_p,n to R_p,n by x ↦ (P_c(W_n(x.val))) for all
colours with p true positions. The relative kernel forces the all-true coordinate to vanish. -/
def naiveStageToRelativeFixedGrade (p n : ℕ) :
    naiveWordFiltration k A I p n →ₗ[k] naiveRelativeSplitWordGradeCoordinates k A I p n :=
  (LinearMap.pi (fun colour : splitWordGradeColours p (n + 1) =>
    naiveStageToSplitWord k A I splitting p n colour.val)).codRestrict
      (naiveRelativeSplitWordGradeSpace k A I p n) (fun x colour hc =>
        relativeNaiveWord_allQuotient_zero k A I splitting n colour.val hc x.val)

private theorem naiveStageToRelativeFixedGrade_reconstruct (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    naiveStageToRelativeFixedGrade k A I splitting p n
        (naiveFixedGradeToStage k A I splitting p n y) = y := by
  apply Subtype.ext
  funext colour
  change splitAmbientToWord k A I splitting colour.val
    (relativeNaiveWordMap k A I n (naiveFixedGradeToRelative k A I splitting p n y)) = y.val colour
  rw [naiveFixedGradeToRelative_word]
  exact naiveFixedGradeToAmbient_coordinate k A I splitting p n y.val colour

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. The kernel of naiveStageToRelativeFixedGrade equals naiveLowerFiltration p n viewed
inside F_p,n. This predecessor is zero at p = 0 and F_(p−1),n otherwise. -/
theorem naiveStageToRelativeFixedGrade_ker (p n : ℕ) :
    LinearMap.ker (naiveStageToRelativeFixedGrade k A I splitting p n) =
      (naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype := by
  classical
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    change naiveStageToRelativeFixedGrade k A I splitting p n x = 0 at hx
    have hfixed (colour : splitWordGradeColours p (n + 1)) :
        naiveStageToSplitWord k A I splitting p n colour.val x = 0 :=
      congrArg (fun y : naiveRelativeSplitWordGradeCoordinates k A I p n => y.val colour) hx
    by_cases hp : p = 0
    · have hall (colour : Fin (n + 1) → Bool) :
          splitAmbientToWord k A I splitting colour (relativeNaiveWordMap k A I n x.val) = 0 := by
        by_cases hc : quotientEntryCount colour = p
        · exact hfixed ⟨colour, hc⟩
        · have hgt : p < quotientEntryCount colour := by omega
          exact naiveStageToSplitWord_zero_of_quotient_count k A I splitting p n colour hgt x
      have hw : relativeNaiveWordMap k A I n x.val = 0 := by
        have h := (splitWord_reconstruct k A I splitting (relativeNaiveWordMap k A I n x.val)).symm
        simpa only [hall, map_zero, Finset.sum_const_zero] using h
      have hx0 : x.val = 0 := (relativeNaiveWordMap_injective k A I n)
        (hw.trans (map_zero (relativeNaiveWordMap k A I n)).symm)
      change (naiveWordFiltration k A I p n).subtype x ∈ naiveLowerFiltration k A I p n
      rw [naiveLowerFiltration, ite_eq_left hp]
      simpa only [Submodule.mem_bot, Submodule.subtype_apply] using hx0
    · have hw : relativeNaiveWordMap k A I n x.val ∈
          idealWordSpan k A I (n + 1) (n + 1 - (p - 1)) := by
        rw [idealWordSpan_eq_splitWordCoordinateStage_comap k A I splitting]
        change ∀ colour : Fin (n + 1) → Bool,
          splitWordIdealPositionCount colour < n + 1 - (p - 1) →
            splitAmbientToWord k A I splitting colour (relativeNaiveWordMap k A I n x.val) = 0
        intro colour hc
        by_cases hq : quotientEntryCount colour = p
        · exact hfixed ⟨colour, hq⟩
        · have hcount := splitWordPositionCounts_add colour
          have hgt : p < quotientEntryCount colour := by omega
          exact naiveStageToSplitWord_zero_of_quotient_count k A I splitting p n colour hgt x
      change (naiveWordFiltration k A I p n).subtype x ∈ naiveLowerFiltration k A I p n
      rw [naiveLowerFiltration, ite_eq_right hp]
      exact hw
  · intro hx
    change naiveStageToRelativeFixedGrade k A I splitting p n x = 0
    apply Subtype.ext
    funext colour
    exact naiveLowerFiltration_le_ker_stageToSplitWord k A I splitting p n colour.val colour.property hx

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. naiveLayerToRelativeFixedGrade maps naiveWordLayer p n = F_p,n/F_lower to R_p,n by
the descended exact-count coordinate maps. -/
def naiveLayerToRelativeFixedGrade (p n : ℕ) :
    naiveWordLayer k A I p n →ₗ[k] naiveRelativeSplitWordGradeCoordinates k A I p n :=
  (naiveLayerToSplitWordCoordinates k A I splitting p n).codRestrict
    (naiveRelativeSplitWordGradeSpace k A I p n) (fun z => by
      refine Submodule.Quotient.induction_on _ z ?_
      intro x colour hc
      change splitAmbientToWord k A I splitting colour.val (relativeNaiveWordMap k A I n x.val) = 0
      exact relativeNaiveWord_allQuotient_zero k A I splitting n colour.val hc x.val)

private theorem naiveLayerToRelativeFixedGrade_projection (p n : ℕ)
    (x : naiveWordFiltration k A I p n) :
    naiveLayerToRelativeFixedGrade k A I splitting p n (naiveWordLayerProjection k A I p n x) =
      naiveStageToRelativeFixedGrade k A I splitting p n x := rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. naiveRelativeFixedGradeToLayer sends y to the class of naiveFixedGradeToStage y
under naiveWordLayerProjection p n. -/
def naiveRelativeFixedGradeToLayer (p n : ℕ) :
    naiveRelativeSplitWordGradeCoordinates k A I p n →ₗ[k] naiveWordLayer k A I p n :=
  (naiveWordLayerProjection k A I p n).comp (naiveFixedGradeToStage k A I splitting p n)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. The composite naiveLayerToRelativeFixedGrade ∘ naiveRelativeFixedGradeToLayer
equals id_(R_p,n). -/
theorem naiveLayerToRelativeFixedGrade_comp_inverse (p n : ℕ) :
    (naiveLayerToRelativeFixedGrade k A I splitting p n).comp
        (naiveRelativeFixedGradeToLayer k A I splitting p n) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  change naiveLayerToRelativeFixedGrade k A I splitting p n
    (naiveWordLayerProjection k A I p n (naiveFixedGradeToStage k A I splitting p n y)) = y
  rw [naiveLayerToRelativeFixedGrade_projection]
  exact naiveStageToRelativeFixedGrade_reconstruct k A I splitting p n y

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. The composite naiveRelativeFixedGradeToLayer ∘ naiveLayerToRelativeFixedGrade
equals the identity on naiveWordLayer p n. -/
theorem naiveRelativeFixedGradeToLayer_comp_extraction (p n : ℕ) :
    (naiveRelativeFixedGradeToLayer k A I splitting p n).comp
        (naiveLayerToRelativeFixedGrade k A I splitting p n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro x
  change naiveWordLayerProjection k A I p n
      (naiveFixedGradeToStage k A I splitting p n
        (naiveLayerToRelativeFixedGrade k A I splitting p n (naiveWordLayerProjection k A I p n x))) =
    naiveWordLayerProjection k A I p n x
  rw [naiveLayerToRelativeFixedGrade_projection]
  have hzero : naiveStageToRelativeFixedGrade k A I splitting p n
      (naiveFixedGradeToStage k A I splitting p n
        (naiveStageToRelativeFixedGrade k A I splitting p n x) - x) = 0 := by
    rw [map_sub, naiveStageToRelativeFixedGrade_reconstruct, sub_self]
  have hl : naiveFixedGradeToStage k A I splitting p n
        (naiveStageToRelativeFixedGrade k A I splitting p n x) - x ∈
      (naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype := by
    rw [← naiveStageToRelativeFixedGrade_ker k A I splitting p n]
    exact hzero
  exact (Submodule.Quotient.eq _).mpr hl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. naiveGradedSplitWordIso : naiveWordLayer p n ≃ₗ[k] R_p,n has forward map
naiveLayerToRelativeFixedGrade and inverse naiveRelativeFixedGradeToLayer, for every p,n : ℕ. -/
def naiveGradedSplitWordIso (p n : ℕ) :
    naiveWordLayer k A I p n ≃ₗ[k] naiveRelativeSplitWordGradeCoordinates k A I p n :=
  { naiveLayerToRelativeFixedGrade k A I splitting p n with
    invFun := naiveRelativeFixedGradeToLayer k A I splitting p n
    left_inv := fun x => congrArg (fun f => f x)
      (naiveRelativeFixedGradeToLayer_comp_extraction k A I splitting p n)
    right_inv := fun y => congrArg (fun f => f y)
      (naiveLayerToRelativeFixedGrade_comp_inverse k A I splitting p n) }

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. For z : naiveWordLayer p n, the underlying family of naiveGradedSplitWordIso z is
naiveLayerToSplitWordCoordinates p n z. -/
theorem naiveGradedSplitWordIso_apply (p n : ℕ) (z : naiveWordLayer k A I p n) :
    (naiveGradedSplitWordIso k A I splitting p n z).val =
      naiveLayerToSplitWordCoordinates k A I splitting p n z := rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I
two-sided. Put Q = A/I and N = n + 1. Choose a k-linear quotient section s. For c : Fin N →
Bool, let W_c be the tensor with I at false and Q at true positions, J_c its ambient
inclusion/section map and P_c its projection/quotient map. Let Γ_p,n = Π c with exactly p true
positions, W_c, and let R_p,n ≤ Γ_p,n impose a zero all-true coordinate. Write K_b for the
naive quotient-map kernel, W_n for its word inclusion in degree n, F_p,n for the pullback of
the span with at least N−p ideal entries, and F_lower for zero at p = 0 or F_(p−1),n
otherwise. For y : R_p,n, naiveGradedSplitWordIso.symm y = naiveWordLayerProjection p n
(naiveFixedGradeToStage p n y). -/
theorem naiveGradedSplitWordIso_symm_apply (p n : ℕ)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) :
    (naiveGradedSplitWordIso k A I splitting p n).symm y =
      naiveWordLayerProjection k A I p n (naiveFixedGradeToStage k A I splitting p n y) := rfl

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
a general word length N, originalCoefficientQuotientWordMap is q_N^V : V ⊗[k] A^⊗N →ₗ[k] V
⊗[k] Q^⊗N. -/
def originalCoefficientQuotientWordMap (N : ℕ) :
    V ⊗[k] TensorPower k N A →ₗ[k] V ⊗[k] TensorPower k N I.Quotient :=
  TensorProduct.map (LinearMap.id : V →ₗ[k] V) (originalQuotientWordMap k A I N)

private theorem barQuotient_word_natural (n : ℕ) :
    (positiveBarWordIso k I.Quotient V n).hom.hom.comp
        ((positiveBarQuotientMap k A I V).f (n + 1)).hom =
      (originalCoefficientQuotientWordMap k A I V (n + 1)).comp
        (positiveBarWordIso k A V n).hom.hom := by
  let e : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 1
  let es : (positiveBarComplex k A V).X (n + 1) ≅ (barComplex k A V).X n :=
    (barComplex k A V).extendXIso e (i := n) rfl
  let et : (positiveBarComplex k I.Quotient V).X (n + 1) ≅ (barComplex k I.Quotient V).X n :=
    (barComplex k I.Quotient V).extendXIso e (i := n) rfl
  let cs : (barComplex k A V).X n ≅
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A) :=
    (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)).toModuleIso
  let ct : (barComplex k I.Quotient V).X n ≅
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) I.Quotient) :=
    (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k I.Quotient n)).toModuleIso
  have hmap : (positiveBarQuotientMap k A I V).f (n + 1) =
      es.hom ≫ (barAlgebraMap (V := V) I.quotientMap).f n ≫ et.inv :=
    HomologicalComplex.extendMap_f (barAlgebraMap (V := V) I.quotientMap) e (i := n) rfl
  have hcoords : (barAlgebraMap (V := V) I.quotientMap).f n ≫ ct.hom =
      cs.hom ≫ ModuleCat.ofHom (originalCoefficientQuotientWordMap k A I V (n + 1)) := by
    apply ModuleCat.hom_ext
    change (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k I.Quotient n)).toLinearMap.comp
        (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (TensorPower.consLevelMap (NonUnitalSubalgebra.Quotient.mkL I) n)) =
      (originalCoefficientQuotientWordMap k A I V (n + 1)).comp
        (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)).toLinearMap
    apply TensorProduct.ext' (M := V) (N := A ⊗[k] TensorPower k n A)
    intro v x
    change TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k I.Quotient n)
        (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (TensorPower.consLevelMap (NonUnitalSubalgebra.Quotient.mkL I) n) (v ⊗ₜ[k] x)) =
      TensorProduct.map (LinearMap.id : V →ₗ[k] V) (originalQuotientWordMap k A I (n + 1))
        (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n) (v ⊗ₜ[k] x))
    rw [TensorProduct.map_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul,
      TensorProduct.map_tmul]
    have h := congrArg (fun f => f x)
      (TensorPower.consEquiv_naturality (NonUnitalSubalgebra.Quotient.mkL I) n)
    exact congrArg (fun y => v ⊗ₜ[k] y) h
  have hcat : (positiveBarQuotientMap k A I V).f (n + 1) ≫
        (positiveBarWordIso k I.Quotient V n).hom =
      (positiveBarWordIso k A V n).hom ≫
        ModuleCat.ofHom (originalCoefficientQuotientWordMap k A I V (n + 1)) := by
    change (positiveBarQuotientMap k A I V).f (n + 1) ≫ (et.hom ≫ ct.hom) =
      (es.hom ≫ cs.hom) ≫ ModuleCat.ofHom (originalCoefficientQuotientWordMap k A I V (n + 1))
    rw [hmap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hcoords]
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
    congrArg (fun f => f.hom) hcat

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N.
relativeBarWordKernelEquiv n identifies K_+.X (n + 1) with ker q_N^V, where K_+ is the
positive bar quotient-map kernel. The equivalence uses kernel preservation under evaluation
and positive word coordinates. -/
def relativeBarWordKernelEquiv (n : ℕ) :
    (relativePositiveBarComplex k A I V).X (n + 1) ≃ₗ[k]
      LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)) :=
  ((PreservesKernel.iso
      (HomologicalComplex.eval (ModuleCat.{max u v w} k) (ComplexShape.down ℕ) (n + 1))
      (positiveBarQuotientMap k A I V)) ≪≫
    ModuleCat.kernelIsoKer ((positiveBarQuotientMap k A I V).f (n + 1))).toLinearEquiv.trans
      ((LinearEquiv.ofEq _ _ (by
        exact kernelWordTransport_eq ((positiveBarQuotientMap k A I V).f (n + 1)).hom
          (originalCoefficientQuotientWordMap k A I V (n + 1))
          (positiveBarWordIso k A V n).toLinearEquiv (positiveBarWordIso k I.Quotient V n).toLinearEquiv
          (barQuotient_word_natural k A I V n))).trans
        ((positiveBarWordIso k A V n).toLinearEquiv.ofSubmodule'
          (LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)))))

/-- Let k be commutative, A a nonunital k-algebra ring, I two-sided and V a k-module. Let K_+ =
ker(positiveBar(A,V) → positiveBar(A/I,V)). For x : K_+.X (n + 1), the ambient coefficient
tensor of relativeBarWordKernelEquiv n x equals relativePositiveBarWordMap n x in V ⊗[k]
A^⊗(n+1). -/
theorem relativeBarWordKernelEquiv_val (n : ℕ)
    (x : (relativePositiveBarComplex k A I V).X (n + 1)) :
    (relativeBarWordKernelEquiv k A I V n x : V ⊗[k] TensorPower k (n + 1) A) =
      relativePositiveBarWordMap k A I V n x := by
  rw [relativeBarWordKernelEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.ofSubmodule'_apply, LinearEquiv.coe_ofEq_apply]
  change (positiveBarWordIso k A V n).toLinearEquiv
      (componentKernelEquiv (positiveBarQuotientMap k A I V) (n + 1) x :
        (positiveBarComplex k A V).X (n + 1)) =
    relativePositiveBarWordMap k A I V n x
  rw [componentKernelEquiv_val, CategoryTheory.Iso.toLinearEquiv_apply]
  rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. For x : K_+.X N and c the all-true colour,
(id_V ⊗ P_c)(W_n^V(x)) = 0, since that coordinate is q_N^V. -/
theorem relativeBarWord_allQuotient_zero (n : ℕ)
    (colour : Fin (n + 1) → Bool) (hc : colour = fun _ => true)
    (x : (relativePositiveBarComplex k A I V).X (n + 1)) :
    coefficientSplitAmbientToWord k A I V splitting colour (relativePositiveBarWordMap k A I V n x) = 0 := by
  subst colour
  change originalCoefficientQuotientWordMap k A I V (n + 1) (relativePositiveBarWordMap k A I V n x) = 0
  rw [← relativeBarWordKernelEquiv_val k A I V n x]
  exact (relativeBarWordKernelEquiv k A I V n x).property

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. barRelativeSplitWordGradeSpace is R_p,n^V, the submodule imposing
that single relative-kernel condition on the exact-count coefficient family. -/
def barRelativeSplitWordGradeSpace (p n : ℕ) :
    Submodule k (barSplitWordGradeCoordinates k A I V p n) where
  carrier := {y | ∀ colour : splitWordGradeColours p (n + 1),
    colour.val = (fun _ => true) → y colour = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy colour hc := by
    change x colour + y colour = (0 : V ⊗[k] splitWordTensor k A I colour.val)
    rw [hx colour hc, hy colour hc, add_zero]
  smul_mem' r x hx colour hc := by
    change r • x colour = (0 : V ⊗[k] splitWordTensor k A I colour.val)
    rw [hx colour hc, smul_zero]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. barRelativeSplitWordGradeCoordinates p n is the module R_p,n^V,
retaining the coefficient V and every exact-p-count colour except for its forced zero all-true
coordinate. -/
abbrev barRelativeSplitWordGradeCoordinates (p n : ℕ) := barRelativeSplitWordGradeSpace k A I V p n

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barFixedGradeToAmbient sends y : Γ_p,n^V to
∑ c with p true positions, (id_V ⊗ J_c)(y_c), in V ⊗[k] A^⊗N. -/
def barFixedGradeToAmbient (p n : ℕ) :
    barSplitWordGradeCoordinates k A I V p n →ₗ[k] V ⊗[k] TensorPower k (n + 1) A :=
  ∑ colour : splitWordGradeColours p (n + 1),
    (coefficientSplitWordToAmbient k A I V splitting colour.val).comp (LinearMap.proj colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem barFixedGradeToAmbient_apply (p n : ℕ)
    (y : barSplitWordGradeCoordinates k A I V p n) :
    barFixedGradeToAmbient k A I splitting V p n y =
      ∑ colour : splitWordGradeColours p (n + 1),
        coefficientSplitWordToAmbient k A I V splitting colour.val (y colour) := by
  simp only [barFixedGradeToAmbient, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem barFixedGradeToAmbient_coordinate (p n : ℕ)
    (y : barSplitWordGradeCoordinates k A I V p n) (target : splitWordGradeColours p (n + 1)) :
    coefficientSplitAmbientToWord k A I V splitting target.val
        (barFixedGradeToAmbient k A I splitting V p n y) = y target := by
  classical
  rw [barFixedGradeToAmbient_apply, map_sum]
  have ht (source : splitWordGradeColours p (n + 1)) :
      coefficientSplitAmbientToWord k A I V splitting target.val
          (coefficientSplitWordToAmbient k A I V splitting source.val (y source)) =
        if source = target then y target else 0 := by
    by_cases h : source = target
    · subst source
      rw [ite_eq_left rfl]
      exact congrArg (fun f => f (y target))
        (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient k A I V splitting target.val)
    · rw [ite_eq_right h]
      exact congrArg (fun f => f (y source))
        (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient_zero
          k A I V splitting source.val target.val (fun hv => h (Subtype.ext hv)))
  simp_rw [ht]
  simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem barFixedGradeToAmbient_quotient_zero (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    originalCoefficientQuotientWordMap k A I V (n + 1)
      (barFixedGradeToAmbient k A I splitting V p n y.val) = 0 := by
  classical
  rw [barFixedGradeToAmbient_apply, map_sum]
  apply Finset.sum_eq_zero
  intro colour _
  by_cases hc : colour.val = fun _ => true
  · rw [y.property colour hc, map_zero, map_zero]
  · change coefficientSplitAmbientToWord k A I V splitting (fun _ : Fin (n + 1) => true)
      (coefficientSplitWordToAmbient k A I V splitting colour.val (y.val colour)) = 0
    exact congrArg (fun f => f (y.val colour))
      (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient_zero
        k A I V splitting colour.val (fun _ => true) hc)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem barFixedGradeToAmbient_mem_span (p n : ℕ)
    (y : barSplitWordGradeCoordinates k A I V p n) :
    barFixedGradeToAmbient k A I splitting V p n y ∈
      coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p) := by
  classical
  rw [barFixedGradeToAmbient_apply]
  apply Submodule.sum_mem
  intro colour _
  have hc := splitWordPositionCounts_add colour.val
  have hq := colour.property
  have hrequired : n + 1 - p ≤ splitWordIdealPositionCount colour.val := by omega
  exact coefficientSplitWordToAmbient_range_le_coefficientIdealWordSpan
    k A I splitting V colour.val (n + 1 - p) hrequired ⟨y colour, rfl⟩

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. Restricting the fixed-count reconstruction
to R_p,n^V gives barFixedGradeToKernel : R_p,n^V →ₗ[k] ker q_N^V. The all-quotient coordinate
is zero and every other colour has an ideal factor. -/
def barFixedGradeToKernel (p n : ℕ) :
    barRelativeSplitWordGradeCoordinates k A I V p n →ₗ[k]
      LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)) :=
  ((barFixedGradeToAmbient k A I splitting V p n).comp
    (barRelativeSplitWordGradeSpace k A I V p n).subtype).codRestrict
      (LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)))
      (by
        intro y
        exact barFixedGradeToAmbient_quotient_zero k A I splitting V p n y)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barFixedGradeToRelative maps R_p,n^V to
K_+.X N by coefficient reconstruction into ker q_N^V followed by relativeBarWordKernelEquiv
n.symm. -/
def barFixedGradeToRelative (p n : ℕ) :
    barRelativeSplitWordGradeCoordinates k A I V p n →ₗ[k]
      (relativePositiveBarComplex k A I V).X (n + 1) :=
  (relativeBarWordKernelEquiv k A I V n).symm.toLinearMap.comp
    (barFixedGradeToKernel k A I splitting V p n)

private theorem barFixedGradeToRelative_word (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    relativePositiveBarWordMap k A I V n (barFixedGradeToRelative k A I splitting V p n y) =
      barFixedGradeToAmbient k A I splitting V p n y.val := by
  have h := congrArg
    (fun z : LinearMap.ker (originalCoefficientQuotientWordMap k A I V (n + 1)) => z.val)
    ((relativeBarWordKernelEquiv k A I V n).apply_symm_apply
      (barFixedGradeToKernel k A I splitting V p n y))
  rw [relativeBarWordKernelEquiv_val] at h
  exact h

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barFixedGradeToStage maps R_p,n^V to B_p,n
by codomain restriction of the reconstructed positive relative term. -/
def barFixedGradeToStage (p n : ℕ) :
    barRelativeSplitWordGradeCoordinates k A I V p n →ₗ[k] barWordFiltration k A I V p n :=
  (barFixedGradeToRelative k A I splitting V p n).codRestrict (barWordFiltration k A I V p n)
    (fun y => by
      change relativePositiveBarWordMap k A I V n (barFixedGradeToRelative k A I splitting V p n y) ∈
        coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p)
      rw [barFixedGradeToRelative_word]
      exact barFixedGradeToAmbient_mem_span k A I splitting V p n y.val)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. For y : R_p,n^V, W_n^V(barFixedGradeToStage
y) = ∑ c with p true positions, (id_V ⊗ J_c)(y_c). -/
theorem barFixedGradeToStage_word (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    relativePositiveBarWordMap k A I V n ((barFixedGradeToStage k A I splitting V p n y).val) =
      ∑ colour : splitWordGradeColours p (n + 1),
        coefficientSplitWordToAmbient k A I V splitting colour.val (y.val colour) := by
  exact (barFixedGradeToRelative_word k A I splitting V p n y).trans
    (barFixedGradeToAmbient_apply k A I splitting V p n y.val)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barStageToRelativeFixedGrade sends x :
B_p,n to the family ((id_V ⊗ P_c)(W_n^V(x.val)))_c in R_p,n^V, for colours with p true
positions. -/
def barStageToRelativeFixedGrade (p n : ℕ) :
    barWordFiltration k A I V p n →ₗ[k] barRelativeSplitWordGradeCoordinates k A I V p n :=
  (LinearMap.pi (fun colour : splitWordGradeColours p (n + 1) =>
    barStageToSplitWord k A I splitting V p n colour.val)).codRestrict
      (barRelativeSplitWordGradeSpace k A I V p n) (fun x colour hc =>
        relativeBarWord_allQuotient_zero k A I splitting V n colour.val hc x.val)

private theorem barStageToRelativeFixedGrade_reconstruct (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    barStageToRelativeFixedGrade k A I splitting V p n
        (barFixedGradeToStage k A I splitting V p n y) = y := by
  apply Subtype.ext
  funext colour
  change coefficientSplitAmbientToWord k A I V splitting colour.val
    (relativePositiveBarWordMap k A I V n (barFixedGradeToRelative k A I splitting V p n y)) = y.val colour
  rw [barFixedGradeToRelative_word]
  exact barFixedGradeToAmbient_coordinate k A I splitting V p n y.val colour

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. The kernel of barStageToRelativeFixedGrade
equals barLowerFiltration p n viewed inside B_p,n. This is zero at p = 0 and B_(p−1),n
otherwise. -/
theorem barStageToRelativeFixedGrade_ker (p n : ℕ) :
    LinearMap.ker (barStageToRelativeFixedGrade k A I splitting V p n) =
      (barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype := by
  classical
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    change barStageToRelativeFixedGrade k A I splitting V p n x = 0 at hx
    have hfixed (colour : splitWordGradeColours p (n + 1)) :
        barStageToSplitWord k A I splitting V p n colour.val x = 0 :=
      congrArg (fun y : barRelativeSplitWordGradeCoordinates k A I V p n => y.val colour) hx
    by_cases hp : p = 0
    · have hall (colour : Fin (n + 1) → Bool) :
          coefficientSplitAmbientToWord k A I V splitting colour
            (relativePositiveBarWordMap k A I V n x.val) = 0 := by
        by_cases hc : quotientEntryCount colour = p
        · exact hfixed ⟨colour, hc⟩
        · have hgt : p < quotientEntryCount colour := by omega
          exact barStageToSplitWord_zero_of_quotient_count k A I splitting V p n colour hgt x
      have hw : relativePositiveBarWordMap k A I V n x.val = 0 := by
        have h := (coefficientSplitWord_reconstruct k A I V splitting
          (relativePositiveBarWordMap k A I V n x.val)).symm
        simpa only [hall, map_zero, Finset.sum_const_zero] using h
      have hx0 : x.val = 0 := (relativePositiveBarWordMap_injective k A I V n)
        (hw.trans (map_zero (relativePositiveBarWordMap k A I V n)).symm)
      change (barWordFiltration k A I V p n).subtype x ∈ barLowerFiltration k A I V p n
      rw [barLowerFiltration, ite_eq_left hp]
      simpa only [Submodule.mem_bot, Submodule.subtype_apply] using hx0
    · have hw : relativePositiveBarWordMap k A I V n x.val ∈
          coefficientIdealWordSpan k A I V (n + 1) (n + 1 - (p - 1)) := by
        rw [coefficientIdealWordSpan_eq_splitWordCoordinateStage_comap k A I splitting V]
        change ∀ colour : Fin (n + 1) → Bool,
          splitWordIdealPositionCount colour < n + 1 - (p - 1) →
            coefficientSplitAmbientToWord k A I V splitting colour
              (relativePositiveBarWordMap k A I V n x.val) = 0
        intro colour hc
        by_cases hq : quotientEntryCount colour = p
        · exact hfixed ⟨colour, hq⟩
        · have hcount := splitWordPositionCounts_add colour
          have hgt : p < quotientEntryCount colour := by omega
          exact barStageToSplitWord_zero_of_quotient_count k A I splitting V p n colour hgt x
      change (barWordFiltration k A I V p n).subtype x ∈ barLowerFiltration k A I V p n
      rw [barLowerFiltration, ite_eq_right hp]
      exact hw
  · intro hx
    change barStageToRelativeFixedGrade k A I splitting V p n x = 0
    apply Subtype.ext
    funext colour
    exact barLowerFiltration_le_ker_stageToSplitWord k A I splitting V p n colour.val colour.property hx

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barLayerToRelativeFixedGrade maps
barWordLayer p n = B_p,n/B_lower to R_p,n^V by the descended exact-count coordinates. -/
def barLayerToRelativeFixedGrade (p n : ℕ) :
    barWordLayer k A I V p n →ₗ[k] barRelativeSplitWordGradeCoordinates k A I V p n :=
  (barLayerToSplitWordCoordinates k A I splitting V p n).codRestrict
    (barRelativeSplitWordGradeSpace k A I V p n) (fun z => by
      refine Submodule.Quotient.induction_on _ z ?_
      intro x colour hc
      change coefficientSplitAmbientToWord k A I V splitting colour.val
        (relativePositiveBarWordMap k A I V n x.val) = 0
      exact relativeBarWord_allQuotient_zero k A I splitting V n colour.val hc x.val)

private theorem barLayerToRelativeFixedGrade_projection (p n : ℕ)
    (x : barWordFiltration k A I V p n) :
    barLayerToRelativeFixedGrade k A I splitting V p n (barWordLayerProjection k A I V p n x) =
      barStageToRelativeFixedGrade k A I splitting V p n x := rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barRelativeFixedGradeToLayer sends y :
R_p,n^V to barWordLayerProjection p n (barFixedGradeToStage y). -/
def barRelativeFixedGradeToLayer (p n : ℕ) :
    barRelativeSplitWordGradeCoordinates k A I V p n →ₗ[k] barWordLayer k A I V p n :=
  (barWordLayerProjection k A I V p n).comp (barFixedGradeToStage k A I splitting V p n)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barLayerToRelativeFixedGrade ∘
barRelativeFixedGradeToLayer = id_(R_p,n^V). -/
theorem barLayerToRelativeFixedGrade_comp_inverse (p n : ℕ) :
    (barLayerToRelativeFixedGrade k A I splitting V p n).comp
        (barRelativeFixedGradeToLayer k A I splitting V p n) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  change barLayerToRelativeFixedGrade k A I splitting V p n
    (barWordLayerProjection k A I V p n (barFixedGradeToStage k A I splitting V p n y)) = y
  rw [barLayerToRelativeFixedGrade_projection]
  exact barStageToRelativeFixedGrade_reconstruct k A I splitting V p n y

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barRelativeFixedGradeToLayer ∘
barLayerToRelativeFixedGrade is the identity on barWordLayer p n. -/
theorem barRelativeFixedGradeToLayer_comp_extraction (p n : ℕ) :
    (barRelativeFixedGradeToLayer k A I splitting V p n).comp
        (barLayerToRelativeFixedGrade k A I splitting V p n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro x
  change barWordLayerProjection k A I V p n
      (barFixedGradeToStage k A I splitting V p n
        (barLayerToRelativeFixedGrade k A I splitting V p n (barWordLayerProjection k A I V p n x))) =
    barWordLayerProjection k A I V p n x
  rw [barLayerToRelativeFixedGrade_projection]
  have hzero : barStageToRelativeFixedGrade k A I splitting V p n
      (barFixedGradeToStage k A I splitting V p n
        (barStageToRelativeFixedGrade k A I splitting V p n x) - x) = 0 := by
    rw [map_sub, barStageToRelativeFixedGrade_reconstruct, sub_self]
  have hl : barFixedGradeToStage k A I splitting V p n
        (barStageToRelativeFixedGrade k A I splitting V p n x) - x ∈
      (barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype := by
    rw [← barStageToRelativeFixedGrade_ker k A I splitting V p n]
    exact hzero
  exact (Submodule.Quotient.eq _).mpr hl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. barGradedSplitWordIso : barWordLayer p n
≃ₗ[k] R_p,n^V has forward map barLayerToRelativeFixedGrade and inverse
barRelativeFixedGradeToLayer, for every p,n : ℕ. -/
def barGradedSplitWordIso (p n : ℕ) :
    barWordLayer k A I V p n ≃ₗ[k] barRelativeSplitWordGradeCoordinates k A I V p n :=
  { barLayerToRelativeFixedGrade k A I splitting V p n with
    invFun := barRelativeFixedGradeToLayer k A I splitting V p n
    left_inv := fun x => congrArg (fun f => f x)
      (barRelativeFixedGradeToLayer_comp_extraction k A I splitting V p n)
    right_inv := fun y => congrArg (fun f => f y)
      (barLayerToRelativeFixedGrade_comp_inverse k A I splitting V p n) }

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. For z : barWordLayer p n, the underlying
family of barGradedSplitWordIso z is barLayerToSplitWordCoordinates p n z. -/
theorem barGradedSplitWordIso_apply (p n : ℕ) (z : barWordLayer k A I V p n) :
    (barGradedSplitWordIso k A I splitting V p n z).val =
      barLayerToSplitWordCoordinates k A I splitting V p n z := rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, Q = A/I and V an arbitrary k-module. Put N = n + 1 and let q_N^V = id_V ⊗ q^⊗N. For
each colour c : Fin N → Bool, let W_c tensor I at false positions and Q at true positions. Let
Γ_p,n^V = Π c with exactly p true positions, V ⊗ W_c, and let R_p,n^V be its submodule with
zero all-true coordinate. Choose a k-linear quotient section s and let J_c,P_c be its word
inclusion/projection maps. Let K_+ = ker(positiveBar(A,V) → positiveBar(Q,V)), W_n^V its
positive word inclusion and B_p,n its ideal-count stage requiring N−p ideal entries. Write
B_lower for zero at p = 0 and B_(p−1),n otherwise. For y : R_p,n^V, barGradedSplitWordIso.symm
y = barWordLayerProjection p n (barFixedGradeToStage y). -/
theorem barGradedSplitWordIso_symm_apply (p n : ℕ)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) :
    (barGradedSplitWordIso k A I splitting V p n).symm y =
      barWordLayerProjection k A I V p n (barFixedGradeToStage k A I splitting V p n y) := rfl

section ExactBoundaries

private theorem quotientEntryCount_allTrue (N : ℕ) :
    quotientEntryCount (fun _ : Fin N => true) = N := by
  classical
  simp [quotientEntryCount]

private theorem sourceCountColour_allTrue {p N : ℕ} (hp : N ≤ p)
    (colour : splitWordGradeColours p N) : colour.val = fun _ => true := by
  classical
  have hcount := splitWordPositionCounts_add colour.val
  have hq := colour.property
  have hz : splitWordIdealPositionCount colour.val = 0 := by omega
  funext i
  cases hi : colour.val i
  · have hmem : i ∈ Finset.univ.filter (fun j : Fin N => colour.val j = false) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    change 0 < splitWordIdealPositionCount colour.val at hpos
    omega
  · rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-module ring, I a k-subalgebra, Q = A/I and N = n + 1.
For a Boolean colour c, let W_c tensor I at false and Q at true positions. Put Γ_p,n = Π c
with exactly p true positions, W_c and let R_p,n impose a zero all-true coordinate. If p < N,
naiveRelativeSplitWordGradeSpace p n = ⊤. No colour with p true positions is the all-true
colour. -/
theorem naiveRelativeSplitWordGradeSpace_eq_top (p n : ℕ) (hp : p < n + 1) :
    naiveRelativeSplitWordGradeSpace k A I p n = ⊤ := by
  apply top_unique
  intro y _ colour hc
  have hq := colour.property
  rw [hc, quotientEntryCount_allTrue] at hq
  omega

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and s a k-linear quotient section. Put N = n + 1, let F_p,n be the relative naive ideal-count
stage, and let R_p,n be the exact-p-count colour family with zero all-quotient coordinate. If
p < N, naiveGradedSplitWordFullIso : naiveWordLayer p n ≃ₗ[k] naiveSplitWordGradeCoordinates p
n is naiveGradedSplitWordIso followed by the equivalence of R_p,n = ⊤ with its full family. -/
def naiveGradedSplitWordFullIso (p n : ℕ) (hp : p < n + 1) :
    naiveWordLayer k A I p n ≃ₗ[k] naiveSplitWordGradeCoordinates k A I p n :=
  (naiveGradedSplitWordIso k A I splitting p n).trans
    (LinearEquiv.ofTop (naiveRelativeSplitWordGradeSpace k A I p n)
      (naiveRelativeSplitWordGradeSpace_eq_top k A I p n hp))

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and s a k-linear quotient section. Put N = n + 1, let F_p,n be the relative naive ideal-count
stage, and let R_p,n be the exact-p-count colour family with zero all-quotient coordinate. If
p < N, naiveGradedSplitWordFullIso z = naiveLayerToSplitWordCoordinates p n z for every z :
naiveWordLayer p n. -/
theorem naiveGradedSplitWordFullIso_apply (p n : ℕ) (hp : p < n + 1)
    (z : naiveWordLayer k A I p n) :
    naiveGradedSplitWordFullIso k A I splitting p n hp z =
      naiveLayerToSplitWordCoordinates k A I splitting p n z := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-module ring, I a k-subalgebra, Q = A/I and N = n + 1.
For a Boolean colour c, let W_c tensor I at false and Q at true positions. Put Γ_p,n = Π c
with exactly p true positions, W_c and let R_p,n impose a zero all-true coordinate. If N ≤ p,
every y : R_p,n equals zero. At p = N the only colour is all-true and is forced zero; at p > N
there are no exact-count colours. -/
theorem naiveRelativeSplitWordGrade_eq_zero (p n : ℕ) (hp : n + 1 ≤ p)
    (y : naiveRelativeSplitWordGradeCoordinates k A I p n) : y = 0 := by
  apply Subtype.ext
  funext colour
  exact y.property colour (sourceCountColour_allTrue hp colour)

include splitting in
/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and s a k-linear quotient section. Put N = n + 1, let F_p,n be the relative naive ideal-count
stage, and let R_p,n be the exact-p-count colour family with zero all-quotient coordinate. If
N ≤ p, every class z : naiveWordLayer p n equals zero, by the relative graded coordinate
equivalence. -/
theorem naiveWordLayer_eq_zero_of_wordLength_le (p n : ℕ) (hp : n + 1 ≤ p)
    (z : naiveWordLayer k A I p n) : z = 0 := by
  apply (naiveGradedSplitWordIso k A I splitting p n).injective
  exact (naiveRelativeSplitWordGrade_eq_zero k A I p n hp
    (naiveGradedSplitWordIso k A I splitting p n z)).trans (map_zero _).symm

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-module ring, I a k-subalgebra, Q = A/I and N = n + 1.
For a Boolean colour c, let W_c tensor I at false and Q at true positions. Put Γ_p,n = Π c
with exactly p true positions, W_c and let R_p,n impose a zero all-true coordinate. Let V be
any k-module and let R_p,n^V ≤ Γ_p,n^V = Π c with p true positions, V ⊗ W_c impose the same
all-true zero coordinate. If p < N, barRelativeSplitWordGradeSpace p n = ⊤ in the full
coefficient exact-count family. -/
theorem barRelativeSplitWordGradeSpace_eq_top (p n : ℕ) (hp : p < n + 1) :
    barRelativeSplitWordGradeSpace k A I V p n = ⊤ := by
  apply top_unique
  intro y _ colour hc
  have hq := colour.property
  rw [hc, quotientEntryCount_allTrue] at hq
  omega

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, s a k-linear quotient section and V any k-module. Put N = n + 1 and let B_p,n be
the relative positive bar word stage in degree N. If p < N, barGradedSplitWordFullIso :
barWordLayer p n ≃ₗ[k] barSplitWordGradeCoordinates p n follows barGradedSplitWordIso by the
top-submodule equivalence. -/
def barGradedSplitWordFullIso (p n : ℕ) (hp : p < n + 1) :
    barWordLayer k A I V p n ≃ₗ[k] barSplitWordGradeCoordinates k A I V p n :=
  (barGradedSplitWordIso k A I splitting V p n).trans
    (LinearEquiv.ofTop (barRelativeSplitWordGradeSpace k A I V p n)
      (barRelativeSplitWordGradeSpace_eq_top k A I V p n hp))

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, s a k-linear quotient section and V any k-module. Put N = n + 1 and let B_p,n be
the relative positive bar word stage in degree N. If p < N, barGradedSplitWordFullIso z =
barLayerToSplitWordCoordinates p n z for every z : barWordLayer p n. -/
theorem barGradedSplitWordFullIso_apply (p n : ℕ) (hp : p < n + 1)
    (z : barWordLayer k A I V p n) :
    barGradedSplitWordFullIso k A I splitting V p n hp z =
      barLayerToSplitWordCoordinates k A I splitting V p n z := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-module ring, I a k-subalgebra, Q = A/I and N = n + 1.
For a Boolean colour c, let W_c tensor I at false and Q at true positions. Put Γ_p,n = Π c
with exactly p true positions, W_c and let R_p,n impose a zero all-true coordinate. Let V be
any k-module and let R_p,n^V ≤ Γ_p,n^V = Π c with p true positions, V ⊗ W_c impose the same
all-true zero coordinate. If N ≤ p, every y : R_p,n^V equals zero, because the all-true
coordinate is killed at p = N and the colour family is empty for p > N. -/
theorem barRelativeSplitWordGrade_eq_zero (p n : ℕ) (hp : n + 1 ≤ p)
    (y : barRelativeSplitWordGradeCoordinates k A I V p n) : y = 0 := by
  apply Subtype.ext
  funext colour
  exact y.property colour (sourceCountColour_allTrue hp colour)

include splitting in
/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, s a k-linear quotient section and V any k-module. Put N = n + 1 and let B_p,n be
the relative positive bar word stage in degree N. If N ≤ p, every class z : barWordLayer p n
equals zero. -/
theorem barWordLayer_eq_zero_of_wordLength_le (p n : ℕ) (hp : n + 1 ≤ p)
    (z : barWordLayer k A I V p n) : z = 0 := by
  apply (barGradedSplitWordIso k A I splitting V p n).injective
  exact (barRelativeSplitWordGrade_eq_zero k A I V p n hp
    (barGradedSplitWordIso k A I splitting V p n z)).trans (map_zero _).symm

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and s a k-linear quotient section. Put N = n + 1, let F_p,n be the relative naive ideal-count
stage, and let R_p,n be the exact-p-count colour family with zero all-quotient coordinate. For
all p,n : ℕ, naiveAssociatedGradedSplitWordIso identifies (naiveAssociatedWordComplex p).X n
with ModuleCat.of k (naiveRelativeSplitWordGradeCoordinates p n). This is the module-category
form of the linear grade equivalence in that degree. -/
def naiveAssociatedGradedSplitWordIso (p n : ℕ) :
    (naiveAssociatedWordComplex k A I p).X n ≅
      ModuleCat.of k (naiveRelativeSplitWordGradeCoordinates k A I p n) :=
  (naiveGradedSplitWordIso k A I splitting p n).toModuleIso

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I
two-sided, s a k-linear quotient section and V any k-module. Put N = n + 1 and let B_p,n be
the relative positive bar word stage in degree N. For all p,n : ℕ,
barAssociatedGradedSplitWordIso identifies (barAssociatedWordComplex p).X (n + 1) with
ModuleCat.of k (barRelativeSplitWordGradeCoordinates p n). It is a degreewise isomorphism of
positive associated terms. -/
def barAssociatedGradedSplitWordIso (p n : ℕ) :
    (barAssociatedWordComplex k A I V p).X (n + 1) ≅
      ModuleCat.of k (barRelativeSplitWordGradeCoordinates k A I V p n) :=
  (barGradedSplitWordIso k A I splitting V p n).toModuleIso


end ExactBoundaries

end ModuleCat.Algebra.Hochschild.NonUnital
