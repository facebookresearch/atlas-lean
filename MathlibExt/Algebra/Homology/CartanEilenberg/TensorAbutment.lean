/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.TensorConvolution
public import MathlibExt.Algebra.Homology.CartanEilenberg.TotalAugmentation
public import Mathlib.RingTheory.Flat.CategoryTheory
import MathlibExt.Algebra.Homology.QuasiIsoColimits

/-!
# Ordinary tensor homology as the Cartan–Eilenberg abutment

Let R be commutative, K,L nonnegative R-module complexes and P a Cartan–Eilenberg resolution of
L. Tensoring the stored column-zero augmentation with id_K gives row augmentations and a
canonical chain map Tot(kunnethCEBicomplex(K,P)) → K ⊗ L.

If every term Kᵢ is flat over R, this chain map is a quasi-isomorphism. Its homology map gives
the canonical abutment isomorphism H_n(Tot(kunnethCEBicomplex(K,P))) ≅ H_n(K ⊗ L). Only the
first complex is required to be degreewise flat.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ}

local instance : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. Tensoring id_K with the stored term-column augmentation P.bicomplex.X₀ → L gives a chain map
from resolution degree zero of the tensor-convolution bicomplex to K ⊗ L. -/
noncomputable def tensorCartanEilenbergColumnZeroMap
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) :
    (kunnethCEBicomplex K P).X 0 ⟶ tensorObj K L :=
  tensorHom (𝟙 K) P.termColumnZeroAugmentation

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. In inner degree q, the column-zero tensor augmentation is exactly the degree-q component of
id_K ⊗ the stored term-column augmentation. -/
theorem tensorCartanEilenbergColumnZeroMap_f
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    (tensorCartanEilenbergColumnZeroMap K P).f q =
      (tensorHom (𝟙 K) P.termColumnZeroAugmentation).f q :=
  rfl

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For each inner total degree q, the flipped tensor-convolution row is augmented to the complex
concentrated in resolution degree zero on (K ⊗ L)_q. -/
noncomputable def tensorCartanEilenbergRowAugmentation
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    (kunnethCEBicomplex K P).flip.X q ⟶
      (ChainComplex.single₀ (ModuleCat.{u} R)).obj ((tensorObj K L).X q) :=
  (ChainComplex.toSingle₀Equiv
    ((kunnethCEBicomplex K P).flip.X q) ((tensorObj K L).X q)).symm
      ⟨(tensorHom (𝟙 K) P.termColumnZeroAugmentation).f q, by
        change ((kunnethCEBicomplex K P).d 1 0).f q ≫
            (tensorHom (𝟙 K) P.termColumnZeroAugmentation).f q = 0
        rw [kunnethCEBicomplex_d]
        change (tensorHom (𝟙 K) (P.bicomplex.d 1 0) ≫
          tensorHom (𝟙 K) P.termColumnZeroAugmentation).f q = 0
        rw [tensorHom_comp_tensorHom,
          P.bicomplex_d_one_zero_comp_termColumnZeroAugmentation]
        simp⟩

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. The resolution-degree-zero component of the degree-q row augmentation is the degree-q
component of id_K ⊗ the term-column augmentation. -/
theorem tensorCartanEilenbergRowAugmentation_f_zero
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    (tensorCartanEilenbergRowAugmentation K P q).f 0 =
      (tensorHom (𝟙 K) P.termColumnZeroAugmentation).f q := by
  unfold tensorCartanEilenbergRowAugmentation
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. The row augmentations in total degrees q+1 and q commute with the inner tensor differential
and the differential of the concentrated target bicomplex. Thus they assemble in q to a
bicomplex map. -/
theorem tensorCartanEilenbergRowAugmentation_comm
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    tensorCartanEilenbergRowAugmentation K P (q + 1) ≫
        (HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj
          (tensorObj K L)).d (q + 1) q =
      (kunnethCEBicomplex K P).flip.d (q + 1) q ≫
        tensorCartanEilenbergRowAugmentation K P q := by
  apply (ChainComplex.toSingle₀Equiv
    ((kunnethCEBicomplex K P).flip.X (q + 1)) ((tensorObj K L).X q)).injective
  apply Subtype.ext
  change (tensorCartanEilenbergRowAugmentation K P (q + 1)).f 0 ≫
      (tensorObj K L).d (q + 1) q =
    ((kunnethCEBicomplex K P).X 0).d (q + 1) q ≫
      (tensorCartanEilenbergRowAugmentation K P q).f 0
  rw [tensorCartanEilenbergRowAugmentation_f_zero,
    tensorCartanEilenbergRowAugmentation_f_zero]
  change (tensorCartanEilenbergColumnZeroMap K P).f (q + 1) ≫
      (tensorObj K L).d (q + 1) q =
    ((kunnethCEBicomplex K P).X 0).d (q + 1) q ≫
      (tensorCartanEilenbergColumnZeroMap K P).f q
  exact (tensorCartanEilenbergColumnZeroMap K P).comm (q + 1) q

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. The row augmentations assemble to a map from the flipped tensor-convolution bicomplex to the
bicomplex concentrated in resolution degree zero on the ordinary tensor complex K ⊗ L. -/
noncomputable def tensorCartanEilenbergRowAugmentationMap
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) :
    (kunnethCEBicomplex K P).flip ⟶
      HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj
        (tensorObj K L) :=
  ChainComplex.ofHom
    (fun q => tensorCartanEilenbergRowAugmentation K P q)
    (fun q => tensorCartanEilenbergRowAugmentation_comm K P q)

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. Totalizing the row augmentation gives the canonical chain map Tot(kunnethCEBicomplex(K,P)) →
K ⊗ L, oriented from the Cartan–Eilenberg tensor model to the ordinary tensor complex. -/
noncomputable def tensorCartanEilenbergToTensor
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) :
    (kunnethCEBicomplex K P).total (ComplexShape.down ℕ) ⟶ tensorObj K L :=
  ((kunnethCEBicomplex K P).totalFlipIso (ComplexShape.down ℕ)).inv ≫
    HomologicalComplex₂.totalAugmentationDownNat
      (tensorCartanEilenbergRowAugmentationMap K P)

private theorem tensorCartanEilenbergToTensor_eq
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) :
    tensorCartanEilenbergToTensor K P =
      ((kunnethCEBicomplex K P).totalFlipIso (ComplexShape.down ℕ)).inv ≫
        HomologicalComplex₂.totalAugmentationDownNat
          (tensorCartanEilenbergRowAugmentationMap K P) :=
  rfl

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. On a summand of resolution degree zero and inner degree q, the canonical total comparison is
exactly the degree-q component of id_K ⊗ the term-column augmentation. -/
theorem tensorCartanEilenbergToTensor_ιTotal
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    (kunnethCEBicomplex K P).ιTotal (ComplexShape.down ℕ) 0 q q
        (Nat.zero_add q) ≫
      (tensorCartanEilenbergToTensor K P).f q =
    (tensorHom (𝟙 K) P.termColumnZeroAugmentation).f q := by
  unfold tensorCartanEilenbergToTensor
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv,
    ComplexShape.σ_down_ℕ, Nat.zero_mul, pow_zero, one_smul]
  have h :=
    HomologicalComplex₂.ιTotal_comp_totalAugmentationDownNat_zero
      (f := tensorCartanEilenbergRowAugmentationMap K P) q
  have h' :
      (kunnethCEBicomplex K P).flip.ιTotal
          (ComplexShape.down ℕ) q 0 q (Nat.add_zero q) ≫
            (HomologicalComplex₂.totalAugmentationDownNat
              (tensorCartanEilenbergRowAugmentationMap K P)).f q =
        ((tensorCartanEilenbergRowAugmentationMap K P).f q).f 0 ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
            ((tensorObj K L).X q)).hom :=
    h
  have hid : ((tensorCartanEilenbergRowAugmentationMap K P).f q).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
          ((tensorObj K L).X q)).hom =
      ((tensorCartanEilenbergRowAugmentationMap K P).f q).f 0 := by
    change ((tensorCartanEilenbergRowAugmentationMap K P).f q).f 0 ≫
        𝟙 (((HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj
          (tensorObj K L)).X q).X 0) =
      ((tensorCartanEilenbergRowAugmentationMap K P).f q).f 0
    exact Category.comp_id _
  have hcomponent :
      ((tensorCartanEilenbergRowAugmentationMap K P).f q).f 0 =
        (tensorHom (𝟙 K) P.termColumnZeroAugmentation).f q := by
    change (tensorCartanEilenbergRowAugmentation K P q).f 0 = _
    exact tensorCartanEilenbergRowAugmentation_f_zero K P q
  exact h'.trans (hid.trans hcomponent)

private abbrev tensorAbutmentFiber (q : ℕ) :=
  (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) ⁻¹' {q}

private theorem tensorAbutmentFiber_finite (q : ℕ) :
    Finite (tensorAbutmentFiber q) := by
  let f : tensorAbutmentFiber q → Fin (q + 1) := fun x ↦
    ⟨x.val.1, by
      have hx := x.property
      change x.val.1 + x.val.2 = q at hx
      omega⟩
  exact Finite.of_injective f (by
    rintro ⟨⟨xp, xq⟩, hx⟩ ⟨⟨yp, yq⟩, hy⟩ hxy
    change xp + xq = q at hx
    change yp + yq = q at hy
    dsimp [f] at hxy
    have hp : xp = yp := congrArg Fin.val hxy
    apply Subtype.ext
    apply Prod.ext
    · exact hp
    · change xq = yq
      omega)

attribute [local instance] tensorAbutmentFiber_finite

private theorem tensorAbutmentFiber_property {q : ℕ}
    (ij : tensorAbutmentFiber q) : ij.val.1 + ij.val.2 = q := by
  have h := ij.property
  change ij.val.1 + ij.val.2 = q at h
  exact h

private noncomputable def tensorAbutmentDegreeCocone
    (K Q : ChainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
  Cofan (fun ij : tensorAbutmentFiber q =>
      K.X ij.val.1 ⊗ Q.X ij.val.2) :=
  Cofan.mk ((tensorObj K Q).X q) (fun ij =>
    ιTensorObj K Q ij.val.1 ij.val.2 q (tensorAbutmentFiber_property ij))

private noncomputable def tensorAbutmentDegreeCoconeIsColimit
    (K Q : ChainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    IsColimit (tensorAbutmentDegreeCocone K Q q) where
  desc s := mapBifunctorDesc (fun i j h =>
    s.ι.app ⟨(⟨(i, j), by simpa only [Set.mem_preimage,
      Set.mem_singleton_iff] using h⟩ : tensorAbutmentFiber q)⟩)
  fac s := by
    rintro ⟨⟨i, j⟩, hij⟩
    change ιTensorObj K Q i j q (tensorAbutmentFiber_property ⟨⟨i, j⟩, hij⟩) ≫
      mapBifunctorDesc _ = s.ι.app ⟨⟨⟨i, j⟩, hij⟩⟩
    rw [ι_mapBifunctorDesc]
  uniq s m hm := by
    apply mapBifunctor.hom_ext
    intro i j h
    simpa [tensorAbutmentDegreeCocone] using
      hm ⟨(⟨(i, j), by simpa only [Set.mem_preimage,
        Set.mem_singleton_iff] using h⟩ : tensorAbutmentFiber q)⟩

private noncomputable abbrev tensorAbutmentSourcePiece
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) {q : ℕ}
    (ij : tensorAbutmentFiber q) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((tensorLeft (K.X ij.val.1)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (P.termResolution ij.val.2).complex

private noncomputable def tensorAbutmentSourceDiagram
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    Discrete (tensorAbutmentFiber q) ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  Discrete.functor (tensorAbutmentSourcePiece K P)

private noncomputable def tensorAbutmentSourceInclusion
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) {q : ℕ}
    (ij : tensorAbutmentFiber q) :
    tensorAbutmentSourcePiece K P ij ⟶ (kunnethCEBicomplex K P).flip.X q :=
  ChainComplex.ofHom
    (fun p => ιTensorObj K (P.bicomplex.X p) ij.val.1 ij.val.2 q
      (tensorAbutmentFiber_property ij))
    (fun p => by
      change ιTensorObj K (P.bicomplex.X (p + 1)) ij.val.1 ij.val.2 q
          (tensorAbutmentFiber_property ij) ≫
          ((kunnethCEBicomplex K P).d (p + 1) p).f q =
        (𝟙 (K.X ij.val.1) ⊗ₘ ((P.bicomplex.d (p + 1) p).f ij.val.2)) ≫
          ιTensorObj K (P.bicomplex.X p) ij.val.1 ij.val.2 q
            (tensorAbutmentFiber_property ij)
      exact ιTensorObj_comp_kunnethCEBicomplex_d K P p ij.val.1 ij.val.2 q
        (tensorAbutmentFiber_property ij))

private theorem tensorAbutmentSourceInclusion_f
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) {q : ℕ}
    (ij : tensorAbutmentFiber q) (p : ℕ) :
    (tensorAbutmentSourceInclusion K P ij).f p =
      ιTensorObj K (P.bicomplex.X p) ij.val.1 ij.val.2 q
        (tensorAbutmentFiber_property ij) :=
  rfl

private noncomputable def tensorAbutmentSourceCocone
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    Cocone (tensorAbutmentSourceDiagram K P q) :=
  Cofan.mk ((kunnethCEBicomplex K P).flip.X q)
    (fun ij => tensorAbutmentSourceInclusion K P ij)

private noncomputable def tensorAbutmentSourceDesc
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q p : ℕ)
    {X : ModuleCat.{u} R}
    (f : ∀ ij : tensorAbutmentFiber q,
      (tensorAbutmentSourcePiece K P ij).X p ⟶ X) :
    ((kunnethCEBicomplex K P).flip.X q).X p ⟶ X :=
  mapBifunctorDesc (fun i j h =>
    f (⟨(i, j), by
      change i + j = q
      exact h⟩ : tensorAbutmentFiber q))

private theorem tensorAbutmentSourceInclusion_f_comp_sourceDesc
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q p : ℕ)
    {X : ModuleCat.{u} R}
    (f : ∀ ij : tensorAbutmentFiber q,
      (tensorAbutmentSourcePiece K P ij).X p ⟶ X)
    (ij : tensorAbutmentFiber q) :
    (tensorAbutmentSourceInclusion K P ij).f p ≫
        tensorAbutmentSourceDesc K P q p f = f ij := by
  rcases ij with ⟨⟨i, j⟩, hij⟩
  unfold tensorAbutmentSourceDesc
  have hdesc := ι_mapBifunctorDesc
    (K₁ := K) (K₂ := P.bicomplex.X p)
    (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.down ℕ)
    (j := q)
    (f := fun i j h => f (⟨(i, j), by
      change i + j = q
      exact h⟩ : tensorAbutmentFiber q))
    i j (tensorAbutmentFiber_property ⟨⟨i, j⟩, hij⟩)
  convert hdesc using 1
  rfl

private theorem tensorAbutmentSourceDesc_unique
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q p : ℕ)
    {X : ModuleCat.{u} R}
    (f : ∀ ij : tensorAbutmentFiber q,
      (tensorAbutmentSourcePiece K P ij).X p ⟶ X)
    (m : ((kunnethCEBicomplex K P).flip.X q).X p ⟶ X)
    (hm : ∀ ij : tensorAbutmentFiber q,
      (tensorAbutmentSourceInclusion K P ij).f p ≫ m = f ij) :
    m = tensorAbutmentSourceDesc K P q p f := by
  unfold tensorAbutmentSourceDesc
  apply mapBifunctor.hom_ext
  intro i j h
  have hm' := hm (⟨(i, j), by
    change i + j = q
    exact h⟩ : tensorAbutmentFiber q)
  have hdesc := ι_mapBifunctorDesc
    (K₁ := K) (K₂ := P.bicomplex.X p)
    (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.down ℕ)
    (j := q)
    (f := fun i j h => f (⟨(i, j), by
      change i + j = q
      exact h⟩ : tensorAbutmentFiber q)) i j h
  have hmcanon :
      ιTensorObj K (P.bicomplex.X p) i j q h ≫ m =
        f (⟨(i, j), by
          change i + j = q
          exact h⟩ : tensorAbutmentFiber q) := by
    convert hm' using 1
    rfl
  exact hmcanon.trans hdesc.symm

private noncomputable def tensorAbutmentSourceCoconeIsColimit
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    IsColimit (tensorAbutmentSourceCocone K P q) := by
  apply HomologicalComplex.isColimitOfEval
  intro p
  refine
    { desc := fun s => tensorAbutmentSourceDesc K P q p
        (fun ij => s.ι.app ⟨ij⟩)
      fac := fun s ij => ?_
      uniq := fun s m hm => ?_ }
  · exact tensorAbutmentSourceInclusion_f_comp_sourceDesc K P q p
      (fun ij => s.ι.app ⟨ij⟩) ij.as
  · apply tensorAbutmentSourceDesc_unique K P q p
      (fun ij => s.ι.app ⟨ij⟩) m
    intro ij
    exact hm ⟨ij⟩

private noncomputable abbrev tensorAbutmentTargetPiece
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) {q : ℕ}
    (ij : tensorAbutmentFiber q) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (ChainComplex.single₀ (ModuleCat.{u} R)).obj
    (K.X ij.val.1 ⊗ L.X ij.val.2)

private noncomputable def tensorAbutmentTargetDiagram
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    Discrete (tensorAbutmentFiber q) ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  Discrete.functor (fun ij : tensorAbutmentFiber q =>
    K.X ij.val.1 ⊗ L.X ij.val.2) ⋙
      ChainComplex.single₀ (ModuleCat.{u} R)

private noncomputable def tensorAbutmentTargetCocone
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    Cocone (tensorAbutmentTargetDiagram K L q) :=
  (ChainComplex.single₀ (ModuleCat.{u} R)).mapCocone
    (tensorAbutmentDegreeCocone K L q)

private noncomputable def tensorAbutmentTargetCoconeIsColimit
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    IsColimit (tensorAbutmentTargetCocone K L q) :=
  isColimitOfPreserves (ChainComplex.single₀ (ModuleCat.{u} R))
    (tensorAbutmentDegreeCoconeIsColimit K L q)

private noncomputable def tensorAbutmentComponentAugmentation
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) {q : ℕ}
    (ij : tensorAbutmentFiber q) :
    tensorAbutmentSourcePiece K P ij ⟶ tensorAbutmentTargetPiece K L ij :=
  ((tensorLeft (K.X ij.val.1)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (P.termResolution ij.val.2).π ≫
    (singleMapHomologicalComplex (tensorLeft (K.X ij.val.1))
      (ComplexShape.down ℕ) 0).hom.app (L.X ij.val.2)

private noncomputable def tensorAbutmentComponentMap
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ) :
    tensorAbutmentSourceDiagram K P q ⟶ tensorAbutmentTargetDiagram K L q :=
  Discrete.natTrans (fun ij => tensorAbutmentComponentAugmentation K P ij.as)

private theorem tensorAbutmentComponentAugmentation_quasiIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) {q : ℕ}
    (hK : ∀ i : ℕ, Module.Flat R (K.X i))
    (ij : tensorAbutmentFiber q) :
    QuasiIso (tensorAbutmentComponentAugmentation K P ij) := by
  let _ : Module.Flat R (K.X ij.val.1) := hK ij.val.1
  let _ : QuasiIso (P.termResolution ij.val.2).π :=
    (P.termResolution ij.val.2).quasiIso
  unfold tensorAbutmentComponentAugmentation
  infer_instance

private theorem tensorAbutmentSourceInclusion_comp_rowAugmentation
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) {q : ℕ}
    (ij : tensorAbutmentFiber q) :
    tensorAbutmentSourceInclusion K P ij ≫
        tensorCartanEilenbergRowAugmentation K P q =
      tensorAbutmentComponentAugmentation K P ij ≫
        (tensorAbutmentTargetCocone K L q).ι.app ⟨ij⟩ := by
  apply HomologicalComplex.hom_ext
  intro p
  cases p with
  | zero =>
      simp only [HomologicalComplex.comp_f]
      change ιTensorObj K (P.bicomplex.X 0) ij.val.1 ij.val.2 q
          (tensorAbutmentFiber_property ij) ≫
          (tensorHom (𝟙 K) P.termColumnZeroAugmentation).f q =
        (𝟙 (K.X ij.val.1) ⊗ₘ (P.termResolution ij.val.2).π.f 0) ≫
          ιTensorObj K L ij.val.1 ij.val.2 q
            (tensorAbutmentFiber_property ij)
      rw [ιTensorObj_tensorHom, P.termColumnZeroAugmentation_f]
      simp only [HomologicalComplex.id_f]
      rfl
  | succ p =>
      exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 (K.X ij.val.1 ⊗ L.X ij.val.2) (p + 1)
          (Nat.succ_ne_zero p)).eq_of_tgt _ _

private theorem tensorCartanEilenbergRowAugmentation_quasiIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ i : ℕ, Module.Flat R (K.X i)) (q : ℕ) :
    QuasiIso (tensorCartanEilenbergRowAugmentation K P q) := by
  let _ : Finite (tensorAbutmentFiber q) := tensorAbutmentFiber_finite q
  let _ : HasExactColimitsOfShape (Discrete (tensorAbutmentFiber q))
      (ModuleCat.{u} R) := inferInstance
  let _ : (colim (J := Discrete (tensorAbutmentFiber q))
      (C := ModuleCat.{u} R)).PreservesHomology := inferInstance
  apply HomologicalComplex.quasiIso_of_isColimit_of_objectwise
    (tensorAbutmentComponentMap K P q)
    (tensorAbutmentSourceCocone K P q)
    (tensorAbutmentTargetCocone K L q)
    (tensorAbutmentSourceCoconeIsColimit K P q)
    (tensorAbutmentTargetCoconeIsColimit K L q)
    (tensorCartanEilenbergRowAugmentation K P q)
  · intro ij
    exact tensorAbutmentSourceInclusion_comp_rowAugmentation K P ij.as
  · intro ij
    exact tensorAbutmentComponentAugmentation_quasiIso K P hK ij.as

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. Assume every Kᵢ is a flat R-module. Then the canonical comparison from the total
Cartan–Eilenberg tensor model to K ⊗ L is a quasi-isomorphism. No flatness of L is assumed. -/
theorem quasiIso_tensorCartanEilenbergToTensor_of_degreewise_flat
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ i : ℕ, Module.Flat R (K.X i)) :
    QuasiIso (tensorCartanEilenbergToTensor K P) := by
  let _ : QuasiIso (HomologicalComplex₂.total.map
      (tensorCartanEilenbergRowAugmentationMap K P) (ComplexShape.down ℕ)) :=
    HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant
      (tensorCartanEilenbergRowAugmentationMap K P)
      (fun q => tensorCartanEilenbergRowAugmentation_quasiIso K P hK q)
  rw [tensorCartanEilenbergToTensor_eq]
  unfold HomologicalComplex₂.totalAugmentationDownNat
  infer_instance

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. If every Kᵢ is flat, the canonical comparison induces an isomorphism
H_n(Tot(kunnethCEBicomplex(K,P))) ≅ H_n(K ⊗ L), for every n ∈ ℕ. -/
noncomputable def tensorCartanEilenbergAbutmentIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ i : ℕ, Module.Flat R (K.X i)) (n : ℕ) :
    ((kunnethCEBicomplex K P).total (ComplexShape.down ℕ)).homology n ≅
      (tensorObj K L).homology n := by
  let _ : QuasiIso (tensorCartanEilenbergToTensor K P) :=
    quasiIso_tensorCartanEilenbergToTensor_of_degreewise_flat K P hK
  exact asIso (HomologicalComplex.homologyMap
    (tensorCartanEilenbergToTensor K P) n)

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. Assume every Kᵢ is flat. In degree n, the forward abutment isomorphism is precisely the
homology map of the canonical chain comparison Tot(kunnethCEBicomplex(K,P)) → K ⊗ L. -/
theorem tensorCartanEilenbergAbutmentIso_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ i : ℕ, Module.Flat R (K.X i)) (n : ℕ) :
    (tensorCartanEilenbergAbutmentIso K P hK n).hom =
      HomologicalComplex.homologyMap (tensorCartanEilenbergToTensor K P) n :=
  rfl

end HomologicalComplex

end
