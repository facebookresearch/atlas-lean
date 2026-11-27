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
# The positive ideal image is the bottom word-count stage

Extend the V-coefficient bar inclusion I → A into positive word-length grading. Its composite
with the quotient A → A/I is zero, so it lifts to the relative positive kernel. The
degree-zero component is zero, and in degree n + 1 its word value is identity on V tensored
with the inclusion of each of the n + 1 ideal entries.

The all-ideal coefficient word span is the range of this tensorized inclusion. Through the
injective kernel word map, its image equals barWordFiltration 0 n. These are image statements
for arbitrary V, without a split-quotient assumption.
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. positiveBarIdealMap is i_+, obtained by extending barAlgebraMap
I.subtypeHom along n ↦ n + 1. -/
abbrev positiveBarIdealMap : positiveBarComplex k I.Algebra V ⟶ positiveBarComplex k A V :=
  HomologicalComplex.extendMap (barAlgebraMap (V := V) I.subtypeHom)
    (ComplexShape.embeddingDown'Add (1 : ℕ) 1)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. i_+ ≫ q_+ = 0 as a chain map from positiveBar(I,V) to
positiveBar(A/I,V). -/
theorem positiveBarIdeal_quotient_zero :
    positiveBarIdealMap k A I V ≫ positiveBarQuotientMap k A I V = 0 := by
  let e : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 1
  change HomologicalComplex.extendMap (barAlgebraMap (V := V) I.subtypeHom)
      e ≫ HomologicalComplex.extendMap (barAlgebraMap (V := V) I.quotientMap) e = 0
  rw [← HomologicalComplex.extendMap_comp, barIdeal_quotient_zero k A I V,
    HomologicalComplex.extendMap_zero]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. idealToRelativePositiveBarComplex is the kernel lift j_+ :
positiveBar(I,V) ⟶ K_+ defined by the zero composite i_+ ≫ q_+. -/
def idealToRelativePositiveBarComplex :
    positiveBarComplex k I.Algebra V ⟶ relativePositiveBarComplex k A I V :=
  kernel.lift (positiveBarQuotientMap k A I V) (positiveBarIdealMap k A I V)
    (positiveBarIdeal_quotient_zero k A I V)

@[reassoc]
theorem idealToRelativePositiveBarComplex_ι :
    idealToRelativePositiveBarComplex k A I V ≫ kernel.ι (positiveBarQuotientMap k A I V) =
      positiveBarIdealMap k A I V := kernel.lift_ι _ _ _

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. For N : ℕ, j_+.f N ≫ (kernel.ι q_+).f N = i_+.f N. -/
theorem idealToRelativePositiveBarComplex_ι_f (n : ℕ) :
    (idealToRelativePositiveBarComplex k A I V).f n ≫
        (kernel.ι (positiveBarQuotientMap k A I V)).f n =
      (positiveBarIdealMap k A I V).f n := by
  simpa only [HomologicalComplex.comp_f] using
    congrArg
      (fun f : positiveBarComplex k I.Algebra V ⟶ positiveBarComplex k A V => f.f n)
      (idealToRelativePositiveBarComplex_ι k A I V)

omit [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. For n : ℕ, i_+.f (n + 1) equals the base component
(barAlgebraMap I.subtypeHom).f n conjugated by the source and target extension object
isomorphisms. -/
theorem positiveBarIdealMap_f (n : ℕ) :
    (positiveBarIdealMap k A I V).f (n + 1) =
      ((barComplex k I.Algebra V).extendXIso
        (ComplexShape.embeddingDown'Add (1 : ℕ) 1) (i := n) rfl).hom ≫
      (barAlgebraMap (V := V) I.subtypeHom).f n ≫
      ((barComplex k A V).extendXIso
        (ComplexShape.embeddingDown'Add (1 : ℕ) 1) (i := n) rfl).inv :=
  HomologicalComplex.extendMap_f (barAlgebraMap (V := V) I.subtypeHom)
    (ComplexShape.embeddingDown'Add (1 : ℕ) 1) (i := n) rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. The component j_+.f 0 is zero, since positiveBar(I,V).X 0 is a
zero object. -/
theorem idealToRelativePositiveBarComplex_f_zero :
    (idealToRelativePositiveBarComplex k A I V).f 0 = 0 :=
  (positiveBarComplex_isZero_zero k I.Algebra V).eq_of_src _ _

omit [I.IsTwoSided] in
/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. For n : ℕ, i_+.f (n+1) followed by positiveBarWordIso_A n
equals positiveBarWordIso_I n followed by id_V ⊗ PiTensorProduct.map (fun _ => I.subtypeHom). -/
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
/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For N : ℕ,
coefficientIdealWordSpan V N N equals range(id_V ⊗ inclusion_I^⊗N) in V ⊗[k] A^⊗N. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For n : ℕ,
relativePositiveBarWordMap n : K_+.X (n + 1) → V ⊗[k] A^⊗(n+1) is injective. -/
theorem relativePositiveBarWordMap_injective (n : ℕ) :
    Function.Injective (relativePositiveBarWordMap k A I V n) := by
  let g := ((kernel.ι (positiveBarQuotientMap k A I V)).f (n + 1)).hom
  have hg : Function.Injective g :=
    (ModuleCat.mono_iff_injective
      ((kernel.ι (positiveBarQuotientMap k A I V)).f (n + 1))).mp inferInstance
  exact (positiveBarWordIso k A V n).toLinearEquiv.injective.comp hg

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. For n : ℕ, relativePositiveBarWordMap n ∘ j_+.f (n+1) = (id_V ⊗
inclusion_I^⊗(n+1)) ∘ positiveBarWordIso_I n.hom. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. For x in positiveBar(I,V).X (n + 1), the word value of j_+(x)
equals id_V ⊗ inclusion_I^⊗(n+1) applied to its positive ideal word coordinate. -/
theorem relativePositiveBarWordMap_idealToRelative_apply (n : ℕ)
    (x : (positiveBarComplex k I.Algebra V).X (n + 1)) :
    relativePositiveBarWordMap k A I V n
        (((idealToRelativePositiveBarComplex k A I V).f (n + 1)).hom x) =
      TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        (PiTensorProduct.map (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A)))
        ((positiveBarWordIso k I.Algebra V n).hom.hom x) :=
  congrArg (fun f => f x) (relativePositiveBarWordMap_idealToRelative k A I V n)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. For v : V and a : Fin (n + 1) → I, lifting the positive word v
⊗ tprod a through j_+ and reading its ambient word yields v ⊗ tprod(i ↦ I.subtypeHom(a_i)). -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. Let i_+ :
positiveBar(I,V) → positiveBar(A,V) be the extended ideal inclusion, q_+ the quotient map and
j_+ its lift to K_+ = ker q_+. For n : ℕ, barWordFiltration 0 n = range (j_+.f (n + 1)).hom in
the relative positive kernel's degree n + 1. -/
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
