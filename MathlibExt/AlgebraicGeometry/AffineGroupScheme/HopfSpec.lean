/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/AlgebraicGeometry/AffineGroupScheme/HopfSpec.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import MathlibExt.Algebra.Coalgebra.Convolution
public import MathlibExt.AlgebraicGeometry.Morphisms.Finite.Basic

/-!
# Infrastructure for Hopf spectra

This file computes the underlying scheme maps of Mathlib's `AlgebraicGeometry.hopfSpec` on an
arbitrary same-universe commutative Hopf algebra.  It identifies the underlying scheme with the
ordinary spectrum, the structural morphism with the algebra structure map, the multiplication
source with the standard affine fibre product, and the group operations with the counit,
comultiplication, and antipode.

It also records coordinate equality and extensionality lemmas obtained from the full faithfulness
of `hopfSpec`.

These lemmas provide the common projection boundary used by concrete affine group schemes.  The
same-universe restriction is inherited from Mathlib's current `hopfSpec` construction.

## Main declarations

* `MathlibExt.hopfSpec_obj_X_left`: the underlying scheme of a Hopf spectrum.
* `MathlibExt.hopfSpec_obj_X_hom`: its structural morphism.
* `MathlibExt.hopfSpec_obj_eq_asOver`: its bundled identification with the group object on the
  ordinary spectrum.
* `MathlibExt.hopfSpec_obj_tensor_X_left`: the source of its multiplication.
* `MathlibExt.algSpec_map_left_ofAlgHom`: the underlying spectrum map of an algebra morphism.
* `MathlibExt.hopfSpec_obj_one_left`, `MathlibExt.hopfSpec_obj_mul_left`, and
  `MathlibExt.hopfSpec_obj_inv_left`: its three group operations.
* `CommHopfAlgCat.preimage_unop_comp_eq_of_hopfSpec_map_comp_eq` and
  `CommHopfAlgCat.hom_ext_of_preimage_unop_eq`: coordinate equalities and
  extensionality transported through the full faithfulness of `hopfSpec`.
* `MathlibExt.isCocomm_iff_isCommMonObj_hopfSpec`: cocommutativity corresponds to a commutative
  group object.
* `MathlibExt.instIsCommMonObjHopfSpec`: a cocommutative Hopf algebra has a commutative Hopf
  spectrum.
* `MathlibExt.moduleFinite_iff_isFinite_hopfSpec`: module-finiteness corresponds to a finite
  structural morphism.
* `MathlibExt.moduleFlat_iff_flat_hopfSpec`: module-flatness corresponds to a flat structural
  morphism.
* `MathlibExt.algebraFinitePresentation_iff_locallyOfFinitePresentation_hopfSpec`: finite
  presentation of an algebra corresponds to local finite presentation of its structural morphism.
* `MathlibExt.moduleProjective_iff_flat_and_finitePresentation`: a finite algebra is projective as a
  module exactly when it is flat and finitely presented as an algebra.
* `MathlibExt.moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec`: the corresponding
  characterization in terms of the structural morphism of a Hopf spectrum.
* `MathlibExt.finrank_hopfSpec`: the rank function of a finite flat Hopf spectrum is the local rank
  of its coordinate algebra.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj

open AlgebraicGeometry MonObj MonoidalCategory

universe u

variable (R : Type u) [CommRing R]

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {K Y : _root_.CommHopfAlgCat.{u} R}

/-- **Coordinate equalities transport through `hopfSpec`, one map at a time.** If two
homomorphisms of affine group schemes out of `Spec Q` agree after composing with the homomorphism
represented by a coordinate morphism `c : Q ⟶ K`, then their coordinate preimages agree after
composing with `c`. -/
theorem preimage_unop_comp_eq_of_hopfSpec_map_comp_eq {Q : _root_.CommHopfAlgCat.{u} R}
    (c : Q ⟶ K)
    (φ ψ : (hopfSpec (CommRingCat.of R)).obj (Opposite.op Q) ⟶
      (hopfSpec (CommRingCat.of R)).obj (Opposite.op Y))
    (hc : (hopfSpec (CommRingCat.of R)).map c.op ≫ φ =
      (hopfSpec (CommRingCat.of R)).map c.op ≫ ψ) :
    ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage φ).unop ≫ c =
      ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage ψ).unop ≫ c := by
  refine Quiver.Hom.op_inj
    ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_injective ?_)
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, Quiver.Hom.op_unop,
    Quiver.Hom.op_unop, (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage,
    (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage]
  exact hc

/-- **Coordinate extensionality transports through `hopfSpec`.** Two homomorphisms of affine
group schemes between Hopf spectra are equal as soon as their coordinate preimages are. -/
theorem hom_ext_of_preimage_unop_eq {Q : _root_.CommHopfAlgCat.{u} R}
    (φ ψ : (hopfSpec (CommRingCat.of R)).obj (Opposite.op Q) ⟶
      (hopfSpec (CommRingCat.of R)).obj (Opposite.op Y))
    (h : ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage φ).unop =
      ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage ψ).unop) :
    φ = ψ := by
  have hop : (hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage φ =
      (hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage ψ := Quiver.Hom.unop_inj h
  rw [← (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage φ,
    ← (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage ψ, hop]

end CommHopfAlgCat

namespace MathlibExt

/-- The scheme underlying the Hopf spectrum of `H` is its ordinary spectrum. -/
@[simp↓]
lemma hopfSpec_obj_X_left (H : CommHopfAlgCat.{u} R) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X.left = Spec (CommRingCat.of H) :=
  rfl

/-- The structural morphism of a Hopf spectrum is induced by its algebra structure map. -/
@[simp↓]
lemma hopfSpec_obj_X_hom (H : CommHopfAlgCat.{u} R) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X.hom =
        eqToHom (hopfSpec_obj_X_left R H) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R H)) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op H)).X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      (hopfSpec_obj_X_left R H) rfl).2 (by
        exact heq_of_eq (AlgebraicGeometry.algSpec_obj_hom
          (R := CommRingCat.of R) (Opposite.op (CommAlgCat.of R H))))

/-- A morphism property holds for the structural morphism of a Hopf spectrum exactly when it holds
for the spectrum map induced by the algebra structure map. -/
theorem morphismProperty_hopfSpec_obj_X_hom_iff
    (P : MorphismProperty Scheme.{u}) (H : CommHopfAlgCat.{u} R) :
    P (((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) ↔
      P (Spec.map (CommRingCat.ofHom (algebraMap R H))) := by
  have h : ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)).X.hom ≍
      Spec.map (CommRingCat.ofHom (algebraMap R H)) := by
    rw [hopfSpec_obj_X_hom]
    exact eqToHom_comp_heq _ _
  -- The two schemes agree by `hopfSpec_obj_X_left`, so the heterogeneous equality is an equality.
  cases hopfSpec_obj_X_left R H
  rw [eq_of_heq h]
  rfl

/-- The multiplication source of a Hopf spectrum is the standard affine fibre product of two
copies of its underlying spectrum over the base. -/
@[simp↓]
lemma hopfSpec_obj_tensor_X_left (H : CommHopfAlgCat.{u} R) :
    ((((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X ⊗
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
          (Opposite.op H)).X).left) =
      Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        (Spec.map (CommRingCat.ofHom (algebraMap R H))) := by
  rw [Over.tensorObj_left]
  have h : ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X.hom ≍
        Spec.map (CommRingCat.ofHom (algebraMap R H)) := by
    rw [hopfSpec_obj_X_hom]
    exact eqToHom_comp_heq _ _
  cases hopfSpec_obj_X_left R H
  exact congrArg (fun k ↦ Limits.pullback k k) (eq_of_heq h)

/-- For commutative $R$-algebras $A$, $B$ and an $R$-algebra homomorphism $f : A \to B$, the
morphism of schemes underlying `algSpec` applied to $f$ is `Spec.map` of the underlying ring
homomorphism of $f$, a morphism $\operatorname{Spec} B \to \operatorname{Spec} A$. -/
@[simp↓]
lemma algSpec_map_left_ofAlgHom {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    ((AlgebraicGeometry.algSpec (CommRingCat.of R)).map
      (CommAlgCat.ofHom f).op).left =
        Spec.map (CommRingCat.ofHom f) := by
  rw [AlgebraicGeometry.algSpec_map_left, ← AlgHom.toRingHom_eq_coe]
  rfl

/-- The Hopf spectrum of a commutative Hopf algebra $H$ over $R$ is $\operatorname{Spec} H$ as a
scheme over $\operatorname{Spec} R$ (`(Spec H).asOver (Spec R)`), with the group structure given
by the counit, comultiplication and antipode of $H$. -/
lemma hopfSpec_obj_eq_asOver (H : CommHopfAlgCat.{u} R) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H) =
      Grp.mk ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :=
  rfl

/-- The unit of a Hopf spectrum is induced by the counit of its coordinate Hopf algebra. -/
@[simp]
lemma hopfSpec_obj_one_left (H : CommHopfAlgCat.{u} R) :
    η[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X].left =
      Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H)) ≫
        eqToHom (hopfSpec_obj_X_left R H).symm := by
  simpa only [eqToHom_refl, Category.id_comp] using
    (conj_eqToHom_iff_heq
      η[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op H)).X].left
      (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H)))
      rfl (hopfSpec_obj_X_left R H)).2 (by
        rw [hopfSpec_obj_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.one_spec_asOver_spec_left
          (R := CommRingCat.of R) (A := CommRingCat.of H)))

/-- Multiplication on a Hopf spectrum is induced by the comultiplication of its coordinate Hopf
algebra. -/
@[simp]
lemma hopfSpec_obj_mul_left (H : CommHopfAlgCat.{u} R) :
    μ[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X].left =
      eqToHom (hopfSpec_obj_tensor_X_left R H) ≫
        (pullbackSpecIso R H H).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R H)) ≫
        eqToHom (hopfSpec_obj_X_left R H).symm := by
  simpa only [Category.assoc] using
    (conj_eqToHom_iff_heq
      μ[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op H)).X].left
      ((pullbackSpecIso R H H).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R H)))
      (hopfSpec_obj_tensor_X_left R H) (hopfSpec_obj_X_left R H)).2 (by
        rw [hopfSpec_obj_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.mul_spec_asOver_spec_left
          (R := CommRingCat.of R) (A := CommRingCat.of H)))

/-- Inversion on a Hopf spectrum is induced by the antipode of its coordinate Hopf algebra. -/
@[simp]
lemma hopfSpec_obj_inv_left (H : CommHopfAlgCat.{u} R) :
    ι[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X].left =
      eqToHom (hopfSpec_obj_X_left R H) ≫
        Spec.map (CommRingCat.ofHom (HopfAlgebra.antipodeAlgHom R H)) ≫
        eqToHom (hopfSpec_obj_X_left R H).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (hopfSpec_obj_X_left R H) (hopfSpec_obj_X_left R H)).2
  rw [hopfSpec_obj_eq_asOver]
  exact heq_of_eq (algSpec_map_left_ofAlgHom R
    (HopfAlgebra.antipodeAlgHom R H))

/-- A Hopf spectrum is a commutative group object exactly when its coordinate Hopf algebra is
cocommutative. -/
theorem isCocomm_iff_isCommMonObj_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    Coalgebra.IsCocomm R H ↔
      IsCommMonObj
        (((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)).X) := by
  constructor
  · intro h
    let _ := h
    rw [hopfSpec_obj_eq_asOver]
    infer_instance
  · intro h
    rw [hopfSpec_obj_eq_asOver] at h
    let _ := h
    constructor
    let leftPoint : WithConv (H →ₐ[R] TensorProduct R H H) :=
      toConv (Algebra.TensorProduct.includeLeft
        (R := R) (A := H) (B := H))
    let rightPoint : WithConv (H →ₐ[R] TensorProduct R H H) :=
      toConv (Algebra.TensorProduct.includeRight
        (R := R) (A := H) (B := H))
    have hcomm : leftPoint * rightPoint = rightPoint * leftPoint := by
      apply (AlgebraicGeometry.Spec.mapMulEquiv
        (R := R) (S := H) (T := TensorProduct R H H)).injective
      simpa only [map_mul] using mul_comm
        ((AlgebraicGeometry.Spec.mapMulEquiv
          (R := R) (S := H) (T := TensorProduct R H H)) leftPoint)
        ((AlgebraicGeometry.Spec.mapMulEquiv
          (R := R) (S := H) (T := TensorProduct R H H)) rightPoint)
    have hswap :
        toConv ((Algebra.TensorProduct.comm R H H).toAlgHom.comp
          (Bialgebra.comulAlgHom R H)) = rightPoint * leftPoint := by
      rw [Bialgebra.toConv_comp_comulAlgHom]
      simp only [leftPoint, rightPoint,
        Algebra.TensorProduct.comm_comp_includeLeft,
        Algebra.TensorProduct.comm_comp_includeRight]
    have hcomul :
        toConv ((Algebra.TensorProduct.comm R H H).toAlgHom.comp
          (Bialgebra.comulAlgHom R H)) =
            toConv (Bialgebra.comulAlgHom R H) := by
      rw [hswap, ← hcomm]
      exact Bialgebra.comulPoint_eq_include_mul.symm
    have hlinear := congrArg
      (fun f : WithConv (H →ₐ[R] TensorProduct R H H) => f.ofConv.toLinearMap) hcomul
    simp only [AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_comulAlgHom] at hlinear
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hlinear x

/-- The Hopf spectrum of a cocommutative Hopf algebra is a commutative group object. -/
instance instIsCommMonObjHopfSpec (H : CommHopfAlgCat.{u} R) [Coalgebra.IsCocomm R H] :
    IsCommMonObj (((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)).X) :=
  (isCocomm_iff_isCommMonObj_hopfSpec R H).mp inferInstance

/-- A Hopf spectrum is finite over its base exactly when its coordinate algebra is
module-finite. -/
theorem moduleFinite_iff_isFinite_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    Module.Finite R H ↔
      IsFinite (((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) := by
  rw [morphismProperty_hopfSpec_obj_X_hom_iff (P := @IsFinite) R H]
  rw [IsFinite.SpecMap_iff]
  -- `SpecMap_iff` leaves the algebra map behind the `CommRingCat.ofHom` projection.
  change Module.Finite R H ↔ (algebraMap R H).Finite
  exact RingHom.finite_algebraMap.symm

/-- A Hopf spectrum is flat over its base exactly when its coordinate algebra is flat as a
module. -/
theorem moduleFlat_iff_flat_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    Module.Flat R H ↔
      Flat (((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) := by
  rw [morphismProperty_hopfSpec_obj_X_hom_iff (P := @Flat) R H]
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.symm

/-- A Hopf spectrum is locally of finite presentation over its base exactly when its coordinate
algebra is finitely presented. -/
theorem algebraFinitePresentation_iff_locallyOfFinitePresentation_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    Algebra.FinitePresentation R H ↔
      LocallyOfFinitePresentation
        (((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) := by
  rw [morphismProperty_hopfSpec_obj_X_hom_iff
    (P := @LocallyOfFinitePresentation) R H]
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.symm

/-- A finite commutative algebra is projective as a module exactly when it is flat as a module
and finitely presented as an algebra. -/
theorem moduleProjective_iff_flat_and_finitePresentation
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] :
    Module.Projective R A ↔ Module.Flat R A ∧ Algebra.FinitePresentation R A := by
  rw [← Module.FinitePresentation.iff_finitePresentation_of_finite]
  exact ⟨fun h ↦ by
    let _ : Module.Projective R A := h
    exact ⟨inferInstance, Module.finitePresentation_of_projective R A⟩,
    fun h ↦ by
      let _ : Module.Flat R A := h.1
      let _ : Module.FinitePresentation R A := h.2
      exact Module.Flat.projective_of_finitePresentation⟩

/-- For a finite Hopf algebra over a commutative ring, projectivity of the coordinate algebra is
equivalent to flatness and local finite presentation of its Hopf spectrum over the base. -/
theorem moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) [Module.Finite R H] :
    Module.Projective R H ↔
      Flat (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) ∧
        LocallyOfFinitePresentation
          (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) := by
  rw [← moduleFlat_iff_flat_hopfSpec, ←
    algebraFinitePresentation_iff_locallyOfFinitePresentation_hopfSpec]
  exact moduleProjective_iff_flat_and_finitePresentation R H

/-- The rank function of a finite flat Hopf spectrum is the local rank of its coordinate
algebra. -/
@[simp↓]
theorem finrank_hopfSpec (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R)
    [Module.Finite R H] [Module.Flat R H] (x : PrimeSpectrum R) :
    (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom).finrank x =
      Module.rankAtStalk (R := R) H x := by
  let _ : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R H))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R H))) :=
    (Flat.SpecMap_iff).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [hopfSpec_obj_X_hom, Scheme.Hom.finrank_comp_left_of_isIso]
  exact Scheme.Hom.finrank_SpecMap_algebraMap R H x

end MathlibExt
