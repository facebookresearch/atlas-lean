/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.IdealCountFaces

/-!
# The ideal image equals the bottom naive filtration stage

A word of length N has at least N ideal entries exactly when every entry belongs to I. Hence
the all-ideal tensor span is the range of the tensorized inclusion I^⊗N → A^⊗N.

The relative naive word map is injective because it is a quotient-kernel inclusion in tensor
coordinates. Comparing the ideal-to-kernel map through that inclusion identifies its component
range with F_0. This proves the image equality without assuming a splitting of the ideal
sequence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct NonUnitalSubalgebra.Quotient

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-module ring and I a k-subalgebra. For a : Fin n → A, n ≤
idealEntryCount a if and only if a_i ∈ I for every i : Fin n. -/
theorem idealEntryCount_length_le_iff {n : ℕ} (a : Fin n → A) :
    n ≤ idealEntryCount k A I a ↔ ∀ i, a i ∈ I.toSubmodule := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => a i ∈ I.toSubmodule)
  constructor
  · intro h i
    change n ≤ S.card at h
    have hsub : S ⊆ Finset.univ := fun j _ => Finset.mem_univ j
    have hcard : (Finset.univ : Finset (Fin n)).card ≤ S.card := by simpa using h
    have heq : S = Finset.univ := Finset.eq_of_subset_of_card_le hsub hcard
    have hi : i ∈ S := heq.symm ▸ Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  · intro h
    have heq : S = Finset.univ := Finset.filter_eq_self.mpr (fun i _ => h i)
    change n ≤ S.card
    rw [heq]
    simp

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-module ring and I a k-subalgebra. For n : ℕ,
idealWordSpan n n equals the range of PiTensorProduct.map (fun _ => I.subtypeHom) : I^⊗n →
A^⊗n. -/
theorem idealWordSpan_all_eq_range (n : ℕ) :
    idealWordSpan k A I n n = LinearMap.range
      (PiTensorProduct.map (fun _ : Fin n => (I.subtypeHom : I.Algebra →ₗ[k] A))) := by
  classical
  rw [PiTensorProduct.map_range_eq_span_tprod]
  unfold idealWordSpan
  apply congrArg (Submodule.span k)
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    let b : Fin n → I.Algebra := fun i => ⟨a i, (idealEntryCount_length_le_iff k A I a).mp ha i⟩
    refine ⟨b, ?_⟩
    apply congrArg (PiTensorProduct.tprod k)
    funext i
    rfl
  · rintro ⟨b, hb⟩
    refine ⟨(fun i => I.subtypeHom (b i)), ?_, hb.symm⟩
    apply (idealEntryCount_length_le_iff k A I _).mpr
    intro i
    exact (b i).property

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. For each n : ℕ, relativeNaiveWordMap n : K_b.X n → A^⊗(n+1) is injective. -/
theorem relativeNaiveWordMap_injective (n : ℕ) :
    Function.Injective (relativeNaiveWordMap k A I n) := by
  let g := ((kernel.ι (cyclicBComplexHom I.quotientMap)).f n).hom
  have hg : Function.Injective g :=
    (ModuleCat.mono_iff_injective ((kernel.ι (cyclicBComplexHom I.quotientMap)).f n)).mp
      inferInstance
  exact (TensorPower.consEquiv k A n).injective.comp hg

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. In degree n, relativeNaiveWordMap composed with idealToRelativeNaiveComplex equals
the tensorized ideal inclusion I^⊗(n+1) → A^⊗(n+1) after TensorPower.consEquiv on the ideal
complex. -/
theorem relativeNaiveWordMap_idealToRelative (n : ℕ) :
    (relativeNaiveWordMap k A I n).comp ((idealToRelativeNaiveComplex k A I).f n).hom =
      (PiTensorProduct.map (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A))).comp
        (TensorPower.consEquiv k I.Algebra n).toLinearMap := by
  have h := congrArg
    (fun f : bComplex k I.Algebra ⟶ bComplex k A => (f.f n).hom)
    (idealToRelativeNaiveComplex_ι k A I)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h
  change (TensorPower.consEquiv k A n).toLinearMap.comp
      (((kernel.ι (cyclicBComplexHom I.quotientMap)).f n).hom.comp
        ((idealToRelativeNaiveComplex k A I).f n).hom) = _
  rw [h, cyclicBComplexHom_f]
  change (TensorPower.consEquiv k A n).toLinearMap.comp
      (TensorPower.consLevelMap (I.subtypeHom : I.Algebra →ₗ[k] A) n) = _
  exact TensorPower.consEquiv_naturality (I.subtypeHom : I.Algebra →ₗ[k] A) n

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication and I a
two-sided nonunital k-subalgebra. Let K_b be the relative naive quotient kernel. Write F_p,n
for naiveWordFiltration p n and L_p,n for its predecessor, zero at p = 0 and F_(p−1),n
otherwise. For n : ℕ, naiveWordFiltration 0 n equals range ((idealToRelativeNaiveComplex).f
n).hom. This is an image equality and uses no split-quotient hypothesis. -/
theorem naiveWordFiltration_zero_eq_range (n : ℕ) :
    naiveWordFiltration k A I 0 n =
      LinearMap.range ((idealToRelativeNaiveComplex k A I).f n).hom := by
  classical
  ext x
  change relativeNaiveWordMap k A I n x ∈ idealWordSpan k A I (n + 1) (n + 1) ↔ _
  rw [idealWordSpan_all_eq_range]
  constructor
  · rintro ⟨y, hy⟩
    let z : (bComplex k I.Algebra).X n := (TensorPower.consEquiv k I.Algebra n).symm y
    refine ⟨z, (relativeNaiveWordMap_injective k A I n) ?_⟩
    have h := congrArg (fun f => f z) (relativeNaiveWordMap_idealToRelative k A I n)
    change relativeNaiveWordMap k A I n (((idealToRelativeNaiveComplex k A I).f n).hom z) =
      PiTensorProduct.map (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A))
        (TensorPower.consEquiv k I.Algebra n z) at h
    have hz : TensorPower.consEquiv k I.Algebra n z = y :=
      (TensorPower.consEquiv k I.Algebra n).apply_symm_apply y
    exact h.trans (hz ▸ hy)
  · rintro ⟨z, rfl⟩
    refine ⟨TensorPower.consEquiv k I.Algebra n z, ?_⟩
    exact (congrArg (fun f => f z) (relativeNaiveWordMap_idealToRelative k A I n)).symm

end ModuleCat.Algebra.Hochschild.NonUnital
