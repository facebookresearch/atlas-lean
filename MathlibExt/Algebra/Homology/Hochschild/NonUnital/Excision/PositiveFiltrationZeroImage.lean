/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationZeroImage
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveBarFiltration

/-!
# Ideal images in positive filtration zero

The positive extension of the coefficient
bar ideal inclusion maps into the quotient
kernel. Its image is the bottom ideal-count
stage in positive word coordinates, with
the augmentation term remaining zero.
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

/-- The original ideal bar inclusion in its native positive word-length placement. -/
abbrev positiveBarIdealMap : positiveBarComplex k I.Algebra V ⟶ positiveBarComplex k A V :=
  HomologicalComplex.extendMap (barAlgebraMap (V := V) I.subtypeHom)
    (ComplexShape.embeddingDown'Add (1 : ℕ) 1)

/-- Native extension preserves the zero ideal-to-quotient bar composite. -/
theorem positiveBarIdeal_quotient_zero :
    positiveBarIdealMap k A I V ≫ positiveBarQuotientMap k A I V = 0 := by
  let e : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 1
  change HomologicalComplex.extendMap (barAlgebraMap (V := V) I.subtypeHom)
      e ≫ HomologicalComplex.extendMap (barAlgebraMap (V := V) I.quotientMap) e = 0
  rw [← HomologicalComplex.extendMap_comp, barIdeal_quotient_zero k A I V,
    HomologicalComplex.extendMap_zero]

/-- The original ideal coefficient bar lands in the positive quotient kernel. -/
def idealToRelativePositiveBarComplex :
    positiveBarComplex k I.Algebra V ⟶ relativePositiveBarComplex k A I V :=
  kernel.lift (positiveBarQuotientMap k A I V) (positiveBarIdealMap k A I V)
    (positiveBarIdeal_quotient_zero k A I V)

@[reassoc]
theorem idealToRelativePositiveBarComplex_ι :
    idealToRelativePositiveBarComplex k A I V ≫ kernel.ι (positiveBarQuotientMap k A I V) =
      positiveBarIdealMap k A I V := kernel.lift_ι _ _ _

/-- Every component retains the original kernel inclusion. -/
theorem idealToRelativePositiveBarComplex_ι_f (n : ℕ) :
    (idealToRelativePositiveBarComplex k A I V).f n ≫
        (kernel.ι (positiveBarQuotientMap k A I V)).f n =
      (positiveBarIdealMap k A I V).f n := by
  simpa only [HomologicalComplex.comp_f] using
    congrArg
      (fun f : positiveBarComplex k I.Algebra V ⟶ positiveBarComplex k A V => f.f n)
      (idealToRelativePositiveBarComplex_ι k A I V)

omit [I.IsTwoSided] in
/-- The original positive ideal map has precisely the native extended bar components. -/
theorem positiveBarIdealMap_f (n : ℕ) :
    (positiveBarIdealMap k A I V).f (n + 1) =
      ((barComplex k I.Algebra V).extendXIso
        (ComplexShape.embeddingDown'Add (1 : ℕ) 1) (i := n) rfl).hom ≫
      (barAlgebraMap (V := V) I.subtypeHom).f n ≫
      ((barComplex k A V).extendXIso
        (ComplexShape.embeddingDown'Add (1 : ℕ) 1) (i := n) rfl).inv :=
  HomologicalComplex.extendMap_f (barAlgebraMap (V := V) I.subtypeHom)
    (ComplexShape.embeddingDown'Add (1 : ℕ) 1) (i := n) rfl

/-- The original ideal-to-kernel map has the zero augmentation component. -/
theorem idealToRelativePositiveBarComplex_f_zero :
    (idealToRelativePositiveBarComplex k A I V).f 0 = 0 :=
  (positiveBarComplex_isZero_zero k I.Algebra V).eq_of_src _ _

omit [I.IsTwoSided] in
/-- Word coordinates retain V and the original ideal inclusion on every original algebra entry. -/
theorem positiveBarIdealMap_word (n : ℕ) :
    (positiveBarIdealMap k A I V).f (n + 1) ≫ (positiveBarWordIso k A V n).hom =
      (positiveBarWordIso k I.Algebra V n).hom ≫
        ModuleCat.ofHom (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (PiTensorProduct.map
            (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A)))) := by
  let e : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 1
  let es : (positiveBarComplex k I.Algebra V).X (n + 1) ≅ (barComplex k I.Algebra V).X n :=
    (barComplex k I.Algebra V).extendXIso e (i := n) rfl
  let et : (positiveBarComplex k A V).X (n + 1) ≅ (barComplex k A V).X n :=
    (barComplex k A V).extendXIso e (i := n) rfl
  let cs : (barComplex k I.Algebra V).X n ≅
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) I.Algebra) :=
    (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k I.Algebra n)).toModuleIso
  let ct : (barComplex k A V).X n ≅
      ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A) :=
    (TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)).toModuleIso
  let m : TensorPower k (n + 1) I.Algebra →ₗ[k] TensorPower k (n + 1) A :=
    PiTensorProduct.map (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A))
  have hmap : (positiveBarIdealMap k A I V).f (n + 1) =
      es.hom ≫ (barAlgebraMap (V := V) I.subtypeHom).f n ≫ et.inv :=
    positiveBarIdealMap_f k A I V n
  have hcoords : (barAlgebraMap (V := V) I.subtypeHom).f n ≫ ct.hom =
      cs.hom ≫ ModuleCat.ofHom (TensorProduct.map (LinearMap.id : V →ₗ[k] V) m) := by
    apply ModuleCat.hom_ext
    change (TensorProduct.congr (LinearEquiv.refl k V)
        (TensorPower.consEquiv k A n)).toLinearMap.comp
        (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (TensorPower.consLevelMap (I.subtypeHom : I.Algebra →ₗ[k] A) n)) =
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V) m).comp
        (TensorProduct.congr (LinearEquiv.refl k V)
          (TensorPower.consEquiv k I.Algebra n)).toLinearMap
    apply TensorProduct.ext' (M := V) (N := I.Algebra ⊗[k] TensorPower k n I.Algebra)
    intro v x
    change TensorProduct.congr (LinearEquiv.refl k V) (TensorPower.consEquiv k A n)
        (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (TensorPower.consLevelMap (I.subtypeHom : I.Algebra →ₗ[k] A) n) (v ⊗ₜ[k] x)) =
      TensorProduct.map (LinearMap.id : V →ₗ[k] V) m
        (TensorProduct.congr (LinearEquiv.refl k V)
          (TensorPower.consEquiv k I.Algebra n) (v ⊗ₜ[k] x))
    rw [TensorProduct.map_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul,
      TensorProduct.map_tmul]
    change v ⊗ₜ[k] TensorPower.consEquiv k A n
        (TensorPower.consLevelMap (I.subtypeHom : I.Algebra →ₗ[k] A) n x) =
      v ⊗ₜ[k] m (TensorPower.consEquiv k I.Algebra n x)
    have hcons := congrArg
      (fun f : (I.Algebra ⊗[k] TensorPower k n I.Algebra) →ₗ[k]
          TensorPower k (n + 1) A => f x)
      (TensorPower.consEquiv_naturality (I.subtypeHom : I.Algebra →ₗ[k] A) n)
    change TensorPower.consEquiv k A n
        (TensorPower.consLevelMap (I.subtypeHom : I.Algebra →ₗ[k] A) n x) =
      m (TensorPower.consEquiv k I.Algebra n x) at hcons
    exact congrArg (fun y : TensorPower k (n + 1) A => v ⊗ₜ[k] y) hcons
  change (positiveBarIdealMap k A I V).f (n + 1) ≫ (et.hom ≫ ct.hom) =
    (es.hom ≫ cs.hom) ≫ ModuleCat.ofHom (TensorProduct.map (LinearMap.id : V →ₗ[k] V) m)
  rw [hmap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hcoords]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The coefficient all-ideal span is the range of the original identity-coefficient tensor map. -/
theorem coefficientIdealWordSpan_all_eq_range (n : ℕ) :
    coefficientIdealWordSpan k A I V n n =
      LinearMap.range (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (PiTensorProduct.map (fun _ : Fin n => (I.subtypeHom : I.Algebra →ₗ[k] A)))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, a, ha, rfl⟩
    have ha' : PiTensorProduct.tprod k a ∈ idealWordSpan k A I n n :=
      Submodule.subset_span ⟨a, ha, rfl⟩
    rw [idealWordSpan_all_eq_range] at ha'
    rcases ha' with ⟨y, hy⟩
    refine ⟨v ⊗ₜ[k] y, ?_⟩
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hy]
  · rw [TensorProduct.range_map_eq_span_tmul]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, y, rfl⟩
    have hy : PiTensorProduct.map (fun _ : Fin n => (I.subtypeHom : I.Algebra →ₗ[k] A)) y ∈
        idealWordSpan k A I n n := by
      rw [idealWordSpan_all_eq_range]
      exact ⟨y, rfl⟩
    have hv : idealWordSpan k A I n n ≤
        (coefficientIdealWordSpan k A I V n n).comap
          (TensorProduct.mk k V (TensorPower k n A) v) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      exact Submodule.subset_span ⟨v, a, ha, rfl⟩
    have hmem := hv hy
    change v ⊗ₜ[k] PiTensorProduct.map
        (fun _ : Fin n => (I.subtypeHom : I.Algebra →ₗ[k] A)) y ∈
      coefficientIdealWordSpan k A I V n n at hmem
    change v ⊗ₜ[k] PiTensorProduct.map
        (fun _ : Fin n => (I.subtypeHom : I.Algebra →ₗ[k] A)) y ∈
      coefficientIdealWordSpan k A I V n n
    exact hmem

/-- The kernel inclusion followed by its original positive word isomorphism is injective. -/
theorem relativePositiveBarWordMap_injective (n : ℕ) :
    Function.Injective (relativePositiveBarWordMap k A I V n) := by
  let g := ((kernel.ι (positiveBarQuotientMap k A I V)).f (n + 1)).hom
  have hg : Function.Injective g :=
    (ModuleCat.mono_iff_injective
      ((kernel.ι (positiveBarQuotientMap k A I V)).f (n + 1))).mp inferInstance
  exact (positiveBarWordIso k A V n).toLinearEquiv.injective.comp hg

/-- The original ideal-to-kernel map has precisely the identity-coefficient word inclusion. -/
theorem relativePositiveBarWordMap_idealToRelative (n : ℕ) :
    (relativePositiveBarWordMap k A I V n).comp
        ((idealToRelativePositiveBarComplex k A I V).f (n + 1)).hom =
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (PiTensorProduct.map
          (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A)))).comp
        (positiveBarWordIso k I.Algebra V n).hom.hom := by
  have hword := congrArg
    (fun f : (positiveBarComplex k I.Algebra V).X (n + 1) ⟶
        (positiveBarComplex k A V).X (n + 1) => f ≫ (positiveBarWordIso k A V n).hom)
    (idealToRelativePositiveBarComplex_ι_f k A I V (n + 1))
  simp only [Category.assoc, positiveBarIdealMap_word] at hword
  apply LinearMap.ext
  intro x
  have hvalue := congrArg
    (fun f : (positiveBarComplex k I.Algebra V).X (n + 1) ⟶
        ModuleCat.of k (V ⊗[k] TensorPower k (n + 1) A) => f.hom x) hword
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hvalue
  exact hvalue

/-- The original word getter evaluates every ideal-complex vector by its tensor inclusion. -/
theorem relativePositiveBarWordMap_idealToRelative_apply (n : ℕ)
    (x : (positiveBarComplex k I.Algebra V).X (n + 1)) :
    relativePositiveBarWordMap k A I V n
        (((idealToRelativePositiveBarComplex k A I V).f (n + 1)).hom x) =
      TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (PiTensorProduct.map (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A)))
        ((positiveBarWordIso k I.Algebra V n).hom.hom x) :=
  congrArg (fun f => f x) (relativePositiveBarWordMap_idealToRelative k A I V n)

/-- The original coefficient is unchanged and every original ideal entry keeps its value and position. -/
theorem relativePositiveBarWordMap_idealToRelative_tprod (n : ℕ) (v : V)
    (a : Fin (n + 1) → I.Algebra) :
    relativePositiveBarWordMap k A I V n
        (((idealToRelativePositiveBarComplex k A I V).f (n + 1)).hom
          ((positiveBarWordIso k I.Algebra V n).inv.hom
            (v ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      v ⊗ₜ[k] PiTensorProduct.tprod k (fun i => I.subtypeHom (a i)) := by
  rw [relativePositiveBarWordMap_idealToRelative_apply]
  have hcoords : (positiveBarWordIso k I.Algebra V n).hom.hom
      ((positiveBarWordIso k I.Algebra V n).inv.hom (v ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      v ⊗ₜ[k] PiTensorProduct.tprod k a :=
    (positiveBarWordIso k I.Algebra V n).toLinearEquiv.apply_symm_apply _
  rw [hcoords, TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod]
  apply congrArg (fun b : Fin (n + 1) → A => v ⊗ₜ[k] PiTensorProduct.tprod k b)
  funext i
  rfl

/-- The bottom positive bar stage is the image of the original arbitrary-coefficient ideal map. -/
theorem barWordFiltration_zero_eq_range (n : ℕ) :
    barWordFiltration k A I V 0 n =
      LinearMap.range ((idealToRelativePositiveBarComplex k A I V).f (n + 1)).hom := by
  classical
  ext x
  change relativePositiveBarWordMap k A I V n x ∈
      coefficientIdealWordSpan k A I V (n + 1) (n + 1) ↔ _
  rw [coefficientIdealWordSpan_all_eq_range]
  constructor
  · rintro ⟨y, hy⟩
    let z : (positiveBarComplex k I.Algebra V).X (n + 1) :=
      (positiveBarWordIso k I.Algebra V n).inv.hom y
    refine ⟨z, (relativePositiveBarWordMap_injective k A I V n) ?_⟩
    have h := relativePositiveBarWordMap_idealToRelative_apply k A I V n z
    have hz : (positiveBarWordIso k I.Algebra V n).hom.hom z = y :=
      (positiveBarWordIso k I.Algebra V n).toLinearEquiv.apply_symm_apply y
    exact h.trans (hz ▸ hy)
  · rintro ⟨z, rfl⟩
    refine ⟨(positiveBarWordIso k I.Algebra V n).hom.hom z, ?_⟩
    exact (relativePositiveBarWordMap_idealToRelative_apply k A I V n z).symm

end ModuleCat.Algebra.Hochschild.NonUnital
