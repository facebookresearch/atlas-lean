/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RepresentationTheory.Rep.Res
public import MathlibExt.CategoryTheory.Monoidal.TensorPowerFunctor
public import MathlibExt.LinearAlgebra.TensorPower.LeadingUnit
public import MathlibExt.LinearAlgebra.PiTensorProduct.FinSnocNaturality

/-!
# Group restriction, tensor products and power coherence

Let k be a commutative ring and G,H groups in universe u.
Group restriction is a strong monoidal functor:
Res(A)⊗Res(B)≅Res(A⊗B), with identity coefficient carrier map,
and its unit isomorphism is the identity on k.

The left-associated positive power L_n(A)=T_(n+1)(A) has n+1 copies
of A with a leading unit, beginning k⊗A. The right-associated power
R_n(A) begins A and recursively prepends A.
A coefficient map Res(A)→B induces maps on all positive powers;
an isomorphism induces power isomorphisms.

The restriction comparisons commute with unit identifications,
head–tail splittings, reassociation, prepended unit maps, identity
and composition. The underlying maps agree with native PiTensorProduct maps on the
coefficient factors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

namespace Rep

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- The actual categorical leading-unit power is canonically the native tensor power.

For `n + 1` coefficient factors, remove the categorical leading unit and retain their
ordered native `Fin (n + 1)` tensor family. -/
noncomputable def tensorPowObjPositiveCarrierEquiv (A : Rep k G) :
    ∀ n : ℕ, (TensorPower.tensorPowObj A (n + 1)).V ≃ₗ[k] TensorPower k (n + 1) A.V
  | 0 => (TensorPower.leadingUnitEquiv (R := k) A.V).symm
  | n + 1 => TensorProduct.congr
      (tensorPowObjPositiveCarrierEquiv A n) (LinearEquiv.refl k A.V) ≪≫ₗ
        (PiTensorProduct.finSnocEquiv k (n + 1) (fun _ : Fin (n + 2) => A.V)).symm

@[simp]
theorem tensorPowObjPositiveCarrierEquiv_zero_tmul
    (A : Rep k G) (r : k) (a : A) :
    tensorPowObjPositiveCarrierEquiv A 0 (r ⊗ₜ[k] a) =
      PiTensorProduct.tprod k (fun _ : Fin 1 => r • a) := by
  simp only [tensorPowObjPositiveCarrierEquiv, TensorPower.leadingUnitEquiv,
    LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    TensorProduct.lid_tmul, PiTensorProduct.subsingletonEquiv_symm_apply']

@[simp]
theorem tensorPowObjPositiveCarrierEquiv_succ_tmul
    (A : Rep k G) (n : ℕ)
    (x : (TensorPower.tensorPowObj A (n + 1)).V) (a : A) :
    tensorPowObjPositiveCarrierEquiv A (n + 1) (x ⊗ₜ[k] a) =
      (PiTensorProduct.finSnocEquiv k (n + 1) (fun _ : Fin (n + 2) => A.V)).symm
        (tensorPowObjPositiveCarrierEquiv A n x ⊗ₜ[k] a) := by
  simp [tensorPowObjPositiveCarrierEquiv]

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For representations A,B, the tensor restriction isomorphism
Res(A)⊗Res(B)≅Res(A⊗B) is the identity on the underlying
tensor module and retains its factor order. -/
noncomputable def resTensorIso (f : H →* G) (A B : Rep k G) :
    Rep.res f A ⊗ Rep.res f B ≅ Rep.res f (A ⊗ B) :=
  eqToIso (by rfl)

@[simp]
theorem resTensorIso_hom_tmul (f : H →* G) (A B : Rep k G)
    (a : A) (b : B) :
    (resTensorIso f A B).hom (a ⊗ₜ[k] b) = a ⊗ₜ[k] b :=
  rfl

@[simp]
theorem resTensorIso_inv_tmul (f : H →* G) (A B : Rep k G)
    (a : A) (b : B) :
    (resTensorIso f A B).inv (a ⊗ₜ[k] b) = a ⊗ₜ[k] b :=
  rfl

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
The tensor restriction isomorphisms and identity-on-k unit
isomorphism give the coherent strong monoidal data of Res. -/
noncomputable def resFunctorCoreMonoidal (f : H →* G) :
    (resFunctor (k := k) f).CoreMonoidal where
  εIso := Iso.refl _
  μIso := resTensorIso f
  μIso_hom_natural_left := by
    intro X Y g Z
    rfl
  μIso_hom_natural_right := by
    intro X Y Z g
    rfl
  associativity := by
    intro X Y Z
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul xy z =>
        induction xy using TensorProduct.inductionOn with
        | tmul x y => rfl
        | add x y hx hy =>
            rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  left_unitality := by
    intro X
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul r x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  right_unitality := by
    intro X
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x r => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Res carries the strong monoidal structure determined by its
tensor and unit isomorphisms on representations. -/
noncomputable instance resFunctorMonoidal (f : H →* G) :
    (resFunctor (k := k) f).Monoidal :=
  (resFunctorCoreMonoidal f).toMonoidal

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For φ:Res(A)→B, the maps M_n:Res(L_n(A))→L_n(B) apply φ
to each A factor. At n=0 the one-factor unitors identify M₀ with φ;
the successor tensors M_n with φ after the inverse tensor restriction
isomorphism. -/
noncomputable def resTensorPowMapSucc
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B) :
    ∀ n : ℕ,
      Rep.res f (TensorPower.tensorPowObj A (n + 1)) ⟶
        TensorPower.tensorPowObj B (n + 1)
  | 0 =>
      (resFunctor f).map (TensorPower.tensorPowObjOneIso A).hom ≫
        phi ≫ (TensorPower.tensorPowObjOneIso B).inv
  | n + 1 =>
      (resTensorIso f (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
        (resTensorPowMapSucc f phi n ⊗ₘ phi)

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For e:Res(A)≅B, the recursive tensor-power maps give
E_n:Res(L_n(A))≅L_n(B), beginning with e under the one-factor unitors. -/
noncomputable def resTensorPowIsoSucc
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (e : Rep.res f A ≅ B) :
    ∀ n : ℕ,
      Rep.res f (TensorPower.tensorPowObj A (n + 1)) ≅
        TensorPower.tensorPowObj B (n + 1)
  | 0 =>
      (resFunctor f).mapIso (TensorPower.tensorPowObjOneIso A) ≪≫
        e ≪≫ (TensorPower.tensorPowObjOneIso B).symm
  | n + 1 =>
      (resTensorIso f (TensorPower.tensorPowObj A (n + 1)) A).symm ≪≫
        tensorIso (resTensorPowIsoSucc f e n) e

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
The restricted head–tail isomorphism is
Res(L_(n+1)(A))≅Res(A)⊗Res(L_n(A)),
obtained from Res(h_A,n) and the inverse tensor restriction comparison. -/
noncomputable def resTensorPowHeadTailIso
    (f : H →* G) (A : Rep k G) (n : ℕ) :
    Rep.res f (TensorPower.tensorPowObj A (n + 2)) ≅
      Rep.res f A ⊗
        Rep.res f (TensorPower.tensorPowObj A (n + 1)) :=
  resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) (n + 1) ≪≫
    TensorPower.tensorPowObjHeadTailIso (Rep.res f A) n ≪≫
    tensorIso (Iso.refl (Rep.res f A))
      (resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n).symm

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
For the restricted head–tail map Ω_n, the square is
Ω_n∘σ_(n+1)⁻¹=(id⊗σ_n⁻¹)∘h_Res(A),n. -/
theorem resTensorPowIsoSucc_inv_comp_resTensorPowHeadTailIso_hom
    (f : H →* G) (A : Rep k G) (n : ℕ) :
    (resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) (n + 1)).inv ≫
        (resTensorPowHeadTailIso f A n).hom =
      (TensorPower.tensorPowObjHeadTailIso (Rep.res f A) n).hom ≫
        (𝟙 (Rep.res f A) ⊗ₘ
          (resTensorPowIsoSucc f
            (Iso.refl (Rep.res f A)) n).inv) := by
  let e := resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) (n + 1)
  let t := TensorPower.tensorPowObjHeadTailIso (Rep.res f A) n
  let d := resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n
  change e.inv ≫ ((e.hom ≫ t.hom) ≫ (𝟙 _ ⊗ₘ d.inv)) =
    t.hom ≫ (𝟙 _ ⊗ₘ d.inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

@[simp]
theorem resTensorPowIsoSucc_hom
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (e : Rep.res f A ≅ B) (n : ℕ) :
    (resTensorPowIsoSucc f e n).hom =
      resTensorPowMapSucc f e.hom n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (resTensorIso f (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
          ((resTensorPowIsoSucc f e n).hom ⊗ₘ e.hom) =
        (resTensorIso f (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
          (resTensorPowMapSucc f e.hom n ⊗ₘ e.hom)
      rw [ih]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
The recursive σ_n is the canonical tensor-power comparison of
the strong monoidal restriction functor, for every n∈ℕ. -/
theorem resTensorPowIsoSucc_refl_eq_mapTensorPowObjIso
    (f : H →* G) (A : Rep k G) :
    ∀ n : ℕ,
      resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n =
        TensorPower.mapTensorPowObjIso (resFunctor f) A (n + 1)
  | 0 => by
      apply Iso.ext
      change (resFunctor f).map (TensorPower.tensorPowObjOneIso A).hom ≫
          (TensorPower.tensorPowObjOneIso (Rep.res f A)).inv =
        (TensorPower.mapTensorPowObjIso (resFunctor f) A 1).hom
      rw [← TensorPower.mapTensorPowObjIso_hom_comp_tensorPowObjOneIso
        (resFunctor f) A]
      simp
  | n + 1 => by
      apply Iso.ext
      change (resTensorIso f
          (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
          ((resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n).hom ⊗ₘ
            𝟙 (Rep.res f A)) =
        (TensorPower.mapTensorPowObjIso
          (resFunctor f) A ((n + 1) + 1)).hom
      rw [TensorPower.mapTensorPowObjIso_succ]
      change (resTensorIso f
          (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
          ((resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n).hom ⊗ₘ
            𝟙 (Rep.res f A)) =
        (resTensorIso f
          (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
          ((TensorPower.mapTensorPowObjIso
            (resFunctor f) A (n + 1)).hom ⊗ₘ 𝟙 (Rep.res f A))
      rw [resTensorPowIsoSucc_refl_eq_mapTensorPowObjIso f A n]

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For e:Res(A)≅B, restriction of the right-associated power is
isomorphic to R_n(B). The comparison starts with e at n=0 and
recursively tensors e with the previous right-power comparison. -/
noncomputable def resTensorPowRightSuccIso
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (e : Rep.res f A ≅ B) :
    ∀ n : ℕ,
      Rep.res f (TensorPower.tensorPowObjRightSucc A n) ≅
        TensorPower.tensorPowObjRightSucc B n
  | 0 => e
  | n + 1 =>
      (resTensorIso f A
        (TensorPower.tensorPowObjRightSucc A n)).symm ≪≫
      tensorIso e (resTensorPowRightSuccIso f e n)

@[simp]
theorem resTensorPowRightSuccIso_zero
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (e : Rep.res f A ≅ B) :
    resTensorPowRightSuccIso f e 0 = e :=
  rfl

@[simp]
theorem resTensorPowRightSuccIso_succ
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (e : Rep.res f A ≅ B) (n : ℕ) :
    resTensorPowRightSuccIso f e (n + 1) =
      (resTensorIso f A
        (TensorPower.tensorPowObjRightSucc A n)).symm ≪≫
      tensorIso e (resTensorPowRightSuccIso f e n) :=
  rfl

@[simp]
theorem resTensorPowMapSucc_zero
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B) :
    resTensorPowMapSucc f phi 0 =
      (resFunctor f).map (TensorPower.tensorPowObjOneIso A).hom ≫
        phi ≫ (TensorPower.tensorPowObjOneIso B).inv :=
  rfl

@[simp]
theorem resTensorPowMapSucc_succ
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B) (n : ℕ) :
    resTensorPowMapSucc f phi (n + 1) =
      (resTensorIso f (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
        (resTensorPowMapSucc f phi n ⊗ₘ phi) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For φ:Res(A)→B and one-factor unitors η_A:L₀(A)≅A,
η_B:L₀(B)≅B, the base map satisfies
M₀∘Res(η_A⁻¹)=η_B⁻¹∘φ. -/
theorem tensorPowObjOneIso_inv_comp_resTensorPowMapSucc_zero
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B) :
    (resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv ≫
        resTensorPowMapSucc f phi 0 =
      phi ≫ (TensorPower.tensorPowObjOneIso B).inv := by
  have hcancel :
      (resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv ≫
          (resFunctor f).map (TensorPower.tensorPowObjOneIso A).hom =
        𝟙 _ := by
    calc
      (resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv ≫
            (resFunctor f).map (TensorPower.tensorPowObjOneIso A).hom =
          (resFunctor f).map
            ((TensorPower.tensorPowObjOneIso A).inv ≫
              (TensorPower.tensorPowObjOneIso A).hom) :=
        ((resFunctor f).map_comp _ _).symm
      _ = (resFunctor f).map (𝟙 A) := by rw [Iso.inv_hom_id]
      _ = 𝟙 _ := (resFunctor f).map_id A
  rw [resTensorPowMapSucc_zero]
  rw [← Category.assoc
    ((resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv)
    ((resFunctor f).map (TensorPower.tensorPowObjOneIso A).hom), hcancel,
    Category.id_comp]

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
For the one-factor unitor η, the canonical inverse power map obeys
σ₀⁻¹∘η_Res(A)⁻¹=Res(η_A⁻¹). -/
theorem tensorPowObjOneIso_inv_comp_resTensorPowIsoSucc_zero_inv
    (f : H →* G) (A : Rep k G) :
    (TensorPower.tensorPowObjOneIso (Rep.res f A)).inv ≫
        (resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) 0).inv =
      (resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv := by
  apply (cancel_mono
    (resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) 0).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [resTensorPowIsoSucc_hom]
  have h := tensorPowObjOneIso_inv_comp_resTensorPowMapSucc_zero
    f (𝟙 (Rep.res f A))
  simpa only [Category.id_comp, Iso.refl_hom] using h.symm

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For e:Res(A)≅B, the inverse base power map E₀⁻¹ followed by
Res(η_A) equals e⁻¹ followed by η_B:
Res(η_A)∘E₀⁻¹=e⁻¹∘η_B. -/
theorem resTensorPowIsoSucc_zero_inv_comp_tensorPowObjOneIso_hom
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (e : Rep.res f A ≅ B) :
    (resTensorPowIsoSucc f e 0).inv ≫
        (resFunctor f).map (TensorPower.tensorPowObjOneIso A).hom =
      (TensorPower.tensorPowObjOneIso B).hom ≫ e.inv := by
  unfold resTensorPowIsoSucc
  change (TensorPower.tensorPowObjOneIso B).hom ≫ e.inv ≫
      (resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv ≫
        (resFunctor f).map (TensorPower.tensorPowObjOneIso A).hom =
    (TensorPower.tensorPowObjOneIso B).hom ≫ e.inv
  rw [← (resFunctor f).map_comp]
  rw [Iso.inv_hom_id, (resFunctor f).map_id]
  simp

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
At n=0, the left-to-right reassociation on Res(A), inverse
right-power restriction, and inverse restricted reassociation compose
to σ₀⁻¹. The right-associated power is just A at this index. -/
theorem resTensorPow_reassociation_coherence_zero
    (f : H →* G) (A : Rep k G) :
    (TensorPower.tensorPowObjRightSuccIso (Rep.res f A) 0).hom ≫
        (resTensorPowRightSuccIso f
          (Iso.refl (Rep.res f A)) 0).inv ≫
        (resFunctor f).map
          (TensorPower.tensorPowObjRightSuccIso A 0).inv =
      (resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) 0).inv := by
  dsimp only [TensorPower.tensorPowObjRightSucc]
  change (TensorPower.tensorPowObjOneIso (Rep.res f A)).hom ≫
      (Iso.refl (Rep.res f A)).inv ≫
      (resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv =
    (resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) 0).inv
  calc
    _ = (TensorPower.tensorPowObjOneIso (Rep.res f A)).hom ≫
        (resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv := by simp
    _ = (TensorPower.tensorPowObjOneIso (Rep.res f A)).hom ≫
        ((TensorPower.tensorPowObjOneIso (Rep.res f A)).inv ≫
          (resTensorPowIsoSucc f
            (Iso.refl (Rep.res f A)) 0).inv) := by
      rw [tensorPowObjOneIso_inv_comp_resTensorPowIsoSucc_zero_inv]
    _ = _ := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
The inverse σ_(n+1)⁻¹ is recovered by head–tail splitting,
id⊗σ_n⁻¹, the tensor restriction isomorphism, and inverse Res(h_A,n).
This is the inverse head–tail coherence equation. -/
theorem resTensorPow_headTail_coherence
    (f : H →* G) (A : Rep k G) (n : ℕ) :
    (TensorPower.tensorPowObjHeadTailIso (Rep.res f A) n).hom ≫
        (𝟙 (Rep.res f A) ⊗ₘ
          (resTensorPowIsoSucc f
            (Iso.refl (Rep.res f A)) n).inv) ≫
        (resTensorIso f A
          (TensorPower.tensorPowObj A (n + 1))).hom ≫
        (resFunctor f).map
          (TensorPower.tensorPowObjHeadTailIso A n).inv =
      (resTensorPowIsoSucc f
        (Iso.refl (Rep.res f A)) (n + 1)).inv := by
  let eTotal := resTensorPowIsoSucc f
    (Iso.refl (Rep.res f A)) (n + 1)
  let eTail := resTensorPowIsoSucc f
    (Iso.refl (Rep.res f A)) n
  have hforward : eTotal.hom ≫
      (TensorPower.tensorPowObjHeadTailIso (Rep.res f A) n).hom =
    (resFunctor f).map
        (TensorPower.tensorPowObjHeadTailIso A n).hom ≫
      (resTensorIso f A
        (TensorPower.tensorPowObj A (n + 1))).inv ≫
      (𝟙 (Rep.res f A) ⊗ₘ eTail.hom) := by
    dsimp only [eTotal, eTail]
    rw [resTensorPowIsoSucc_refl_eq_mapTensorPowObjIso,
      resTensorPowIsoSucc_refl_eq_mapTensorPowObjIso]
    exact TensorPower.mapTensorPowObjIso_hom_headTail
      (resFunctor f) A n
  apply (cancel_epi eTotal.hom).1
  let tail :=
    (𝟙 (Rep.res f A) ⊗ₘ eTail.inv) ≫
    (resTensorIso f A
      (TensorPower.tensorPowObj A (n + 1))).hom ≫
    (resFunctor f).map
      (TensorPower.tensorPowObjHeadTailIso A n).inv
  have hforwardTail := congrArg (fun q => q ≫ tail) hforward
  simp only [tail, Category.assoc] at hforwardTail
  change eTotal.hom ≫
      (TensorPower.tensorPowObjHeadTailIso (Rep.res f A) n).hom ≫
      tail = eTotal.hom ≫ eTotal.inv
  rw [hforwardTail]
  simp only [TensorPower.tensorPowObj_succ, tensor_V, tensor_ρ,
    id_tensorHom, whiskerLeft_hom_inv_assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  rw [← (resFunctor f).map_comp, Iso.hom_inv_id,
    (resFunctor f).map_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
The forward comparison obeys
σ_(n+1)∘Res(h_A,n)⁻¹ =
h_Res(A),n⁻¹∘(id⊗σ_n)∘μ_f⁻¹,
where μ_f is the tensor restriction isomorphism. -/
theorem resTensorPow_headTail_inv_coherence
    (f : H →* G) (A : Rep k G) (n : ℕ) :
    (resFunctor f).map
          (TensorPower.tensorPowObjHeadTailIso A n).inv ≫
        (resTensorPowIsoSucc f
          (Iso.refl (Rep.res f A)) (n + 1)).hom =
      (resTensorIso f A
          (TensorPower.tensorPowObj A (n + 1))).inv ≫
        (𝟙 (Rep.res f A) ⊗ₘ
          (resTensorPowIsoSucc f
            (Iso.refl (Rep.res f A)) n).hom) ≫
        (TensorPower.tensorPowObjHeadTailIso
          (Rep.res f A) n).inv := by
  let eTotal := resTensorPowIsoSucc f
    (Iso.refl (Rep.res f A)) (n + 1)
  let eTail := resTensorPowIsoSucc f
    (Iso.refl (Rep.res f A)) n
  let hA := TensorPower.tensorPowObjHeadTailIso A n
  let hR := TensorPower.tensorPowObjHeadTailIso (Rep.res f A) n
  let t := resTensorIso f A
    (TensorPower.tensorPowObj A (n + 1))
  have hforward : eTotal.hom ≫ hR.hom =
      (resFunctor f).map hA.hom ≫ t.inv ≫
        (𝟙 (Rep.res f A) ⊗ₘ eTail.hom) := by
    dsimp only [eTotal, eTail, hA, hR, t]
    rw [resTensorPowIsoSucc_refl_eq_mapTensorPowObjIso,
      resTensorPowIsoSucc_refl_eq_mapTensorPowObjIso]
    exact TensorPower.mapTensorPowObjIso_hom_headTail
      (resFunctor f) A n
  have hpost := congrArg (fun q => q ≫ hR.inv) hforward
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hpost
  calc
    (resFunctor f).map hA.inv ≫ eTotal.hom =
        (resFunctor f).map hA.inv ≫
          ((resFunctor f).map hA.hom ≫ t.inv ≫
            (𝟙 (Rep.res f A) ⊗ₘ eTail.hom) ≫ hR.inv) := by
      rw [hpost]
    _ = t.inv ≫ (𝟙 (Rep.res f A) ⊗ₘ eTail.hom) ≫ hR.inv := by
      rw [← Category.assoc, ← (resFunctor f).map_comp,
        Iso.inv_hom_id, (resFunctor f).map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
For u:k_triv→A, let u_H be u restricted to H through the unit
isomorphism of Res. The power comparisons satisfy
σ_(n+1)∘Res(prepend_u)=prepend_(u_H)∘σ_n. -/
theorem resTensorPow_prepend_coherence
    (f : H →* G) (A : Rep k G)
    (u : 𝟙_ (Rep k G) ⟶ A) (n : ℕ) :
    (resFunctor f).map (TensorPower.tensorPowPrependMap u n) ≫
        (resTensorPowIsoSucc f
          (Iso.refl (Rep.res f A)) (n + 1)).hom =
      (resTensorPowIsoSucc f
          (Iso.refl (Rep.res f A)) n).hom ≫
        TensorPower.tensorPowPrependMap
          ((resFunctorCoreMonoidal f).εIso.hom ≫
            (resFunctor f).map u) n := by
  unfold TensorPower.tensorPowPrependMap
  rw [(resFunctor f).map_comp, (resFunctor f).map_comp]
  simp only [Category.assoc]
  rw [resTensorPow_headTail_inv_coherence]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
Let r_A,n:L_n(A)≅R_n(A) be reassociation and ρ_n the canonical
right-power restriction comparison. Then
σ_n⁻¹=Res(r_A,n)⁻¹∘ρ_n⁻¹∘r_Res(A),n for every n∈ℕ. -/
theorem resTensorPow_reassociation_coherence
    (f : H →* G) (A : Rep k G) :
    ∀ n : ℕ,
      (TensorPower.tensorPowObjRightSuccIso (Rep.res f A) n).hom ≫
          (resTensorPowRightSuccIso f
            (Iso.refl (Rep.res f A)) n).inv ≫
          (resFunctor f).map
            (TensorPower.tensorPowObjRightSuccIso A n).inv =
        (resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n).inv
  | 0 => resTensorPow_reassociation_coherence_zero f A
  | n + 1 => by
      rw [TensorPower.tensorPowObjRightSuccIso_succ,
        resTensorPowRightSuccIso_succ,
        TensorPower.tensorPowObjRightSuccIso_succ]
      simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
        tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv,
        Category.assoc]
      dsimp only [TensorPower.tensorPowObjRightSucc]
      have hmap :
          resMap f
              ((𝟙 A ⊗ₘ
                  (TensorPower.tensorPowObjRightSuccIso A n).inv) ≫
                (TensorPower.tensorPowObjHeadTailIso A n).inv) =
            resMap f
                (𝟙 A ⊗ₘ
                  (TensorPower.tensorPowObjRightSuccIso A n).inv) ≫
              resMap f
                (TensorPower.tensorPowObjHeadTailIso A n).inv :=
        (resFunctor f).map_comp _ _
      rw [hmap]
      have htensor :
          resMap f
              (𝟙 A ⊗ₘ
                (TensorPower.tensorPowObjRightSuccIso A n).inv) =
            (resTensorIso f A
                (TensorPower.tensorPowObjRightSucc A n)).inv ≫
              (resMap f (𝟙 A) ⊗ₘ
                resMap f
                  (TensorPower.tensorPowObjRightSuccIso A n).inv) ≫
              (resTensorIso f A
                (TensorPower.tensorPowObj A (n + 1))).hom := by
        have hdelta :
            Functor.OplaxMonoidal.δ (resFunctor f) A
                (TensorPower.tensorPowObjRightSucc A n) =
              (resTensorIso f A
                (TensorPower.tensorPowObjRightSucc A n)).inv := by
          rfl
        have hmu :
            Functor.LaxMonoidal.μ (resFunctor f) A
                (TensorPower.tensorPowObj A (n + 1)) =
              (resTensorIso f A
                (TensorPower.tensorPowObj A (n + 1))).hom := by
          rfl
        simpa only [hdelta, hmu] using
          (Functor.Monoidal.map_tensor
            (F := resFunctor f) (𝟙 A)
              (TensorPower.tensorPowObjRightSuccIso A n).inv)
      rw [htensor]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      have hid : resMap f (𝟙 A) = 𝟙 (Rep.res f A) :=
        (resFunctor f).map_id A
      rw [hid]
      rw [tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc]
      simp only [Category.id_comp]
      have hih :
          (TensorPower.tensorPowObjRightSuccIso
              (Rep.res f A) n).hom ≫
            (resTensorPowRightSuccIso f
              (Iso.refl (Rep.res f A)) n).inv ≫
            resMap f
              (TensorPower.tensorPowObjRightSuccIso A n).inv =
          (resTensorPowIsoSucc f
            (Iso.refl (Rep.res f A)) n).inv :=
        resTensorPow_reassociation_coherence f A n
      have hihLeft :
          ((TensorPower.tensorPowObjRightSuccIso
              (Rep.res f A) n).hom ≫
            (resTensorPowRightSuccIso f
              (Iso.refl (Rep.res f A)) n).inv) ≫
            resMap f
              (TensorPower.tensorPowObjRightSuccIso A n).inv =
          (resTensorPowIsoSucc f
            (Iso.refl (Rep.res f A)) n).inv := by
        rw [Category.assoc]
        exact hih
      rw [hihLeft]
      exact resTensorPow_headTail_coherence f A n


/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For φ:Res(A)→B and x∈A, the base power map sends
η_A⁻¹(x) to η_B⁻¹(φ(x)). -/
theorem resTensorPowMapSucc_zero_oneIso_inv_apply
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B) (x : A) :
    (resTensorPowMapSucc f phi 0).hom
        ((TensorPower.tensorPowObjOneIso A).inv.hom x) =
      (TensorPower.tensorPowObjOneIso B).inv.hom (phi.hom x) :=
  ConcreteCategory.congr_hom
    (tensorPowObjOneIso_inv_comp_resTensorPowMapSucc_zero f phi) x

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For r∈k and a∈A, the base power map from Res(k⊗A) to k⊗B
has value r⊗a↦r⊗φ(a). -/
theorem resTensorPowMapSucc_zero_tmul
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B)
    (r : k) (a : A) :
    (resTensorPowMapSucc f phi 0).hom (r ⊗ₜ[k] a) =
      r ⊗ₜ[k] phi.hom a := by
  simp only [Nat.reduceAdd, TensorPower.tensorPowObj_succ,
    TensorPower.tensorPowObj_zero, tensor_V, tensorUnit_V, res_obj_ρ,
    tensor_ρ, tensorUnit_ρ, resTensorPowMapSucc_zero, hom_comp,
    Representation.IntertwiningMap.comp_apply]
  change 1 ⊗ₜ[k] phi.hom (r • a) = r ⊗ₜ[k] phi.hom a
  rw [map_smul, TensorProduct.tmul_smul]
  simpa only [smul_eq_mul, mul_one] using
    (TensorProduct.smul_tmul' (R := k) (R' := k)
      r (1 : k) (phi.hom a))

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For φ:Res(A)→B and x∈Res(L_n(A)), the successor map has value
M_(n+1)(x⊗a)=M_n(x)⊗φ(a). -/
theorem resTensorPowMapSucc_succ_tmul
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B) (n : ℕ)
    (x : Rep.res f (TensorPower.tensorPowObj A (n + 1))) (a : A) :
    (resTensorPowMapSucc f phi (n + 1)).hom (x ⊗ₜ[k] a) =
      (resTensorPowMapSucc f phi n).hom x ⊗ₜ[k] phi.hom a := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Under the representation/module positive-power carrier
equivalences, M_n equals the ordinary positive tensor-power map
of the underlying k-linear coefficient map φ. -/
theorem tensorPowObjPositiveCarrierEquiv_resTensorPowMapSucc
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B) :
    ∀ (n : ℕ)
      (x : Rep.res f (TensorPower.tensorPowObj A (n + 1))),
      tensorPowObjPositiveCarrierEquiv B n
          ((resTensorPowMapSucc f phi n).hom x) =
        PiTensorProduct.map (fun _ : Fin (n + 1) => phi.hom.toLinearMap)
          (tensorPowObjPositiveCarrierEquiv A n x)
  | 0, x => by
      induction x using TensorProduct.inductionOn with
      | tmul r a =>
          rw [resTensorPowMapSucc_zero_tmul,
            tensorPowObjPositiveCarrierEquiv_zero_tmul,
            tensorPowObjPositiveCarrierEquiv_zero_tmul, PiTensorProduct.map_tprod]
          apply congrArg (PiTensorProduct.tprod k)
          funext q
          exact (phi.hom.toLinearMap.map_smul r a).symm
      | add x y hx hy => simp only [map_add, hx, hy]
  | n + 1, x => by
      induction x using TensorProduct.inductionOn with
      | tmul y a =>
          rw [resTensorPowMapSucc_succ_tmul,
            tensorPowObjPositiveCarrierEquiv_succ_tmul,
            tensorPowObjPositiveCarrierEquiv_succ_tmul]
          apply (PiTensorProduct.finSnocEquiv k (n + 1)
            (fun _ : Fin (n + 2) => B.V)).injective
          rw [LinearEquiv.apply_symm_apply]
          have h := LinearMap.congr_fun
            (PiTensorProduct.finSnocEquiv_naturality k (n + 1)
              (fun _ : Fin (n + 2) => A.V) (fun _ : Fin (n + 2) => B.V)
              (fun _ => phi.hom.toLinearMap))
            ((PiTensorProduct.finSnocEquiv k (n + 1)
              (fun _ : Fin (n + 2) => A.V)).symm
              (tensorPowObjPositiveCarrierEquiv A n y ⊗ₜ[k] a))
          simpa only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
            TensorProduct.map_tmul,
            tensorPowObjPositiveCarrierEquiv_resTensorPowMapSucc f phi n y] using h.symm
      | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- For a commutative ring k and G-representation A, the positive
power map induced by id_G and id_A is id_(L_n(A)) in every n. -/
theorem resTensorPowMapSucc_id (A : Rep k G) (n : ℕ) :
    resTensorPowMapSucc (MonoidHom.id G) (𝟙 A) n =
      𝟙 (TensorPower.tensorPowObj A (n + 1)) := by
  induction n with
  | zero =>
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul r a =>
          change k at r
          change (resTensorPowMapSucc (MonoidHom.id G) (𝟙 A) 0).hom
              (r ⊗ₜ[k] a) = r ⊗ₜ[k] a
          rw [resTensorPowMapSucc_zero_tmul]
          rfl
      | add x y hx hy => simp only [map_add, hx, hy]
  | succ n ih =>
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x a =>
          change (resTensorPowMapSucc (MonoidHom.id G) (𝟙 A) (n + 1)).hom
              (x ⊗ₜ[k] a) = x ⊗ₜ[k] a
          rw [resTensorPowMapSucc_succ_tmul]
          rw [show (resTensorPowMapSucc (MonoidHom.id G) (𝟙 A) n).hom x = x by
            exact congrArg (fun h => h.hom x) ih]
          rfl
      | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- For a commutative ring k, G-representations A,B and φ:A→B,
the power map with group map id_G equals the ordinary categorical
tensor-power map T_(n+1)(φ). -/
theorem resTensorPowMapSucc_id_eq_tensorPowMap
    {A B : Rep k G} (phi : A ⟶ B) :
    ∀ n : ℕ,
      resTensorPowMapSucc (MonoidHom.id G) phi n =
        TensorPower.tensorPowMap phi (n + 1)
  | 0 => by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul r a =>
          change (resTensorPowMapSucc (MonoidHom.id G) phi 0).hom
              (r ⊗ₜ[k] a) =
            (TensorPower.tensorPowMap phi 1).hom (r ⊗ₜ[k] a)
          rw [resTensorPowMapSucc_zero_tmul]
          rfl
      | add x y hx hy => simp only [map_add, hx, hy]
  | n + 1 => by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x a =>
          change (resTensorPowMapSucc
              (MonoidHom.id G) phi (n + 1)).hom (x ⊗ₜ[k] a) =
            (TensorPower.tensorPowMap phi (n + 2)).hom (x ⊗ₜ[k] a)
          rw [resTensorPowMapSucc_succ_tmul]
          change (resTensorPowMapSucc (MonoidHom.id G) phi n).hom x ⊗ₜ[k]
              phi.hom a =
            (TensorPower.tensorPowMap phi (n + 1)).hom x ⊗ₜ[k]
              phi.hom a
          rw [resTensorPowMapSucc_id_eq_tensorPowMap phi n]
      | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H,K groups in universe u. For f:H→G, g:K→H,
φ:Res_f(A)→B and ψ:Res_g(B)→C,
M_(f∘g)(ψ∘Res_g(φ))=
M_g(ψ)∘Res_g(M_f(φ)) in every positive power index n. -/
theorem resTensorPowMapSucc_comp
    {K : Type u} [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K}
    (f : H →* G) (g : K →* H)
    (phi : Rep.res f A ⟶ B) (psi : Rep.res g B ⟶ C)
    (n : ℕ) :
    resTensorPowMapSucc (f.comp g)
        ((resFunctor g).map phi ≫ psi) n =
      (resFunctor g).map (resTensorPowMapSucc f phi n) ≫
        resTensorPowMapSucc g psi n := by
  induction n with
  | zero =>
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul r a =>
          change k at r
          change (resTensorPowMapSucc (f.comp g)
              ((resFunctor g).map phi ≫ psi) 0).hom (r ⊗ₜ[k] a) =
            (resTensorPowMapSucc g psi 0).hom
              ((resTensorPowMapSucc f phi 0).hom (r ⊗ₜ[k] a))
          rw [resTensorPowMapSucc_zero_tmul,
            resTensorPowMapSucc_zero_tmul,
            resTensorPowMapSucc_zero_tmul]
          rfl
      | add x y hx hy => simp only [map_add, hx, hy]
  | succ n ih =>
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x a =>
          change (resTensorPowMapSucc (f.comp g)
              ((resFunctor g).map phi ≫ psi) (n + 1)).hom (x ⊗ₜ[k] a) =
            (resTensorPowMapSucc g psi (n + 1)).hom
              ((resTensorPowMapSucc f phi (n + 1)).hom (x ⊗ₜ[k] a))
          rw [resTensorPowMapSucc_succ_tmul,
            resTensorPowMapSucc_succ_tmul,
            resTensorPowMapSucc_succ_tmul]
          rw [show (resTensorPowMapSucc (f.comp g)
              ((resFunctor g).map phi ≫ psi) n).hom x =
            (resTensorPowMapSucc g psi n).hom
              ((resTensorPowMapSucc f phi n).hom x) by
                exact congrArg (fun h => h.hom x) ih]
          rfl
      | add x y hx hy => simp only [map_add, hx, hy]

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For equal group homomorphisms f=g and coefficient maps φ,ψ
with equal underlying k-linear maps, the induced positive power
maps have equal underlying linear maps for every n. -/
theorem resTensorPowMapSucc_congr
    {A : Rep k G} {B : Rep k H}
    {f g : H →* G} (hfg : f = g)
    {phi : Rep.res f A ⟶ B} {psi : Rep.res g A ⟶ B}
    (hphi : phi.hom.toLinearMap = psi.hom.toLinearMap)
    (n : ℕ) :
    (resTensorPowMapSucc f phi n).hom.toLinearMap =
      (resTensorPowMapSucc g psi n).hom.toLinearMap := by
  subst hfg
  have h : phi = psi := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact hphi
  subst h
  rfl

/-- Let k be a commutative ring and G,H,K groups in universe u, f:H→G, g:K→H,
φ:Res_f(A)→B and ψ:Res_g(B)→C.
If h=f∘g and the underlying coefficient map χ equals ψ∘φ,
the underlying map M_h(χ) equals the composite power map from φ and ψ. -/
theorem resTensorPowMapSucc_comp_congr
    {K : Type u} [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K}
    (f : H →* G) (g : K →* H)
    (phi : Rep.res f A ⟶ B) (psi : Rep.res g B ⟶ C)
    {h : K →* G} {chi : Rep.res h A ⟶ C}
    (hh : h = f.comp g)
    (hchi : chi.hom.toLinearMap =
      (((resFunctor g).map phi) ≫ psi).hom.toLinearMap)
    (n : ℕ) :
    (resTensorPowMapSucc h chi n).hom.toLinearMap =
      (((resFunctor g).map (resTensorPowMapSucc f phi n)) ≫
        resTensorPowMapSucc g psi n).hom.toLinearMap := by
  calc
    (resTensorPowMapSucc h chi n).hom.toLinearMap =
        (resTensorPowMapSucc (f.comp g)
          ((resFunctor g).map phi ≫ psi) n).hom.toLinearMap :=
      resTensorPowMapSucc_congr hh hchi n
    _ = (((resFunctor g).map (resTensorPowMapSucc f phi n)) ≫
        resTensorPowMapSucc g psi n).hom.toLinearMap :=
      congrArg (fun t => t.hom.toLinearMap)
        (resTensorPowMapSucc_comp f g phi psi n)

/-- For a commutative ring k and two composable coefficient-map
paths A→B→C and A→B′→C over possibly different intermediate
groups, equality of their underlying k-linear composites implies
equality of the underlying composite positive tensor-power maps,
for every n. The endpoint coefficients are the same. -/
theorem resTensorPowMapSucc_composites_toLinearMap_eq
    {H' K : Type u} [Group H'] [Group K]
    {A : Rep k G} {B : Rep k H} {B' : Rep k H'} {C : Rep k K}
    (f : H →* G) (g : K →* H)
    (phi : Rep.res f A ⟶ B) (psi : Rep.res g B ⟶ C)
    (f' : H' →* G) (g' : K →* H')
    (phi' : Rep.res f' A ⟶ B') (psi' : Rep.res g' B' ⟶ C)
    (h : psi.hom.toLinearMap.comp phi.hom.toLinearMap =
      psi'.hom.toLinearMap.comp phi'.hom.toLinearMap)
    (n : ℕ) :
    (((resFunctor g).map (resTensorPowMapSucc f phi n) ≫
        resTensorPowMapSucc g psi n).hom.toLinearMap) =
      (((resFunctor g').map (resTensorPowMapSucc f' phi' n) ≫
        resTensorPowMapSucc g' psi' n).hom.toLinearMap) := by
  apply LinearMap.ext
  intro x
  apply (tensorPowObjPositiveCarrierEquiv C n).injective
  calc
    tensorPowObjPositiveCarrierEquiv C n
        ((resTensorPowMapSucc g psi n).hom
          ((resTensorPowMapSucc f phi n).hom x)) =
      PiTensorProduct.map (fun _ : Fin (n + 1) => psi.hom.toLinearMap)
        (tensorPowObjPositiveCarrierEquiv B n
          ((resTensorPowMapSucc f phi n).hom x)) :=
      tensorPowObjPositiveCarrierEquiv_resTensorPowMapSucc g psi n _
    _ = PiTensorProduct.map (fun _ : Fin (n + 1) => psi.hom.toLinearMap)
        (PiTensorProduct.map (fun _ : Fin (n + 1) => phi.hom.toLinearMap)
          (tensorPowObjPositiveCarrierEquiv A n x)) := by
      rw [tensorPowObjPositiveCarrierEquiv_resTensorPowMapSucc]
    _ = PiTensorProduct.map (fun _ : Fin (n + 1) =>
        psi.hom.toLinearMap.comp phi.hom.toLinearMap)
        (tensorPowObjPositiveCarrierEquiv A n x) := by
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl
    _ = PiTensorProduct.map (fun _ : Fin (n + 1) =>
        psi'.hom.toLinearMap.comp phi'.hom.toLinearMap)
        (tensorPowObjPositiveCarrierEquiv A n x) := by rw [h]
    _ = PiTensorProduct.map (fun _ : Fin (n + 1) => psi'.hom.toLinearMap)
        (PiTensorProduct.map (fun _ : Fin (n + 1) => phi'.hom.toLinearMap)
          (tensorPowObjPositiveCarrierEquiv A n x)) := by
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl
    _ = PiTensorProduct.map (fun _ : Fin (n + 1) => psi'.hom.toLinearMap)
        (tensorPowObjPositiveCarrierEquiv B' n
          ((resTensorPowMapSucc f' phi' n).hom x)) := by
      rw [tensorPowObjPositiveCarrierEquiv_resTensorPowMapSucc]
    _ = tensorPowObjPositiveCarrierEquiv C n
        ((resTensorPowMapSucc g' psi' n).hom
          ((resTensorPowMapSucc f' phi' n).hom x)) :=
      (tensorPowObjPositiveCarrierEquiv_resTensorPowMapSucc
        g' psi' n _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
For φ:Res(A)→B, its power map factors as
M_n(φ)=T_(n+1)(φ)∘σ_n. -/
theorem resTensorPowMapSucc_eq_refl_comp_tensorPowMap
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B) (n : ℕ) :
    resTensorPowMapSucc f phi n =
      resTensorPowMapSucc f (𝟙 (Rep.res f A)) n ≫
        TensorPower.tensorPowMap phi (n + 1) := by
  have hraw : resTensorPowMapSucc f phi n =
      (resFunctor (MonoidHom.id H)).map
          (resTensorPowMapSucc f (𝟙 (Rep.res f A)) n) ≫
        resTensorPowMapSucc (MonoidHom.id H) phi n := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact resTensorPowMapSucc_comp_congr
      f (MonoidHom.id H) (𝟙 (Rep.res f A)) phi
        (by ext x; rfl) (by rfl) n
  rw [hraw, resTensorPowMapSucc_id_eq_tensorPowMap]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
For φ:Res(A)→B, u:k_triv,G→A and v:k_triv,H→B with
φ∘u_H=v after the unit restriction comparison, the square
M_(n+1)(φ)∘Res(prepend_u)=prepend_v∘M_n(φ) commutes. -/
theorem resTensorPowMapSucc_prepend_naturality
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (phi : Rep.res f A ⟶ B)
    (u : 𝟙_ (Rep k G) ⟶ A)
    (v : 𝟙_ (Rep k H) ⟶ B)
    (huv : ((resFunctorCoreMonoidal f).εIso.hom ≫
      (resFunctor f).map u) ≫ phi = v)
    (n : ℕ) :
    (resFunctor f).map (TensorPower.tensorPowPrependMap u n) ≫
        resTensorPowMapSucc f phi (n + 1) =
      resTensorPowMapSucc f phi n ≫
        TensorPower.tensorPowPrependMap v n := by
  let cₙ := resTensorPowMapSucc f (𝟙 (Rep.res f A)) n
  let cₙ₁ := resTensorPowMapSucc f (𝟙 (Rep.res f A)) (n + 1)
  let u' := (resFunctorCoreMonoidal f).εIso.hom ≫
    (resFunctor f).map u
  let p := TensorPower.tensorPowPrependMap u' n
  calc
    (resFunctor f).map (TensorPower.tensorPowPrependMap u n) ≫
          resTensorPowMapSucc f phi (n + 1) =
      ((resFunctor f).map (TensorPower.tensorPowPrependMap u n) ≫ cₙ₁) ≫
        TensorPower.tensorPowMap phi (n + 2) := by
          rw [resTensorPowMapSucc_eq_refl_comp_tensorPowMap]
          simp only [Category.assoc]
          convert rfl using 1
    _ = (cₙ ≫ p) ≫ TensorPower.tensorPowMap phi (n + 2) := by
      rw [show (resFunctor f).map
            (TensorPower.tensorPowPrependMap u n) ≫ cₙ₁ = cₙ ≫ p by
        dsimp only [cₙ, cₙ₁, p, u']
        have hc := resTensorPow_prepend_coherence f A u n
        rw [resTensorPowIsoSucc_hom,
          resTensorPowIsoSucc_hom] at hc
        exact hc]
    _ = cₙ ≫
        (p ≫ TensorPower.tensorPowMap phi (n + 2)) := by
          simp only [Category.assoc]
    _ = cₙ ≫
        (TensorPower.tensorPowMap phi (n + 1) ≫
          TensorPower.tensorPowPrependMap v n) := by
            rw [← TensorPower.tensorPowMap_comp_tensorPowPrependMap
              phi u' v huv n]
    _ = (cₙ ≫ TensorPower.tensorPowMap phi (n + 1)) ≫
        TensorPower.tensorPowPrependMap v n := by
          simp only [Category.assoc]
    _ = resTensorPowMapSucc f phi n ≫
        TensorPower.tensorPowPrependMap v n := by
          rw [← resTensorPowMapSucc_eq_refl_comp_tensorPowMap]

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
For e:Res(A)≅B, the inverse power isomorphism factors as
E_n⁻¹=σ_n⁻¹∘T_(n+1)(e⁻¹). -/
theorem resTensorPowIsoSucc_inv
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (e : Rep.res f A ≅ B) (n : ℕ) :
    (resTensorPowIsoSucc f e n).inv =
      resTensorPowMapSucc (MonoidHom.id H) e.inv n ≫
        (resTensorPowIsoSucc f
          (Iso.refl (Rep.res f A)) n).inv := by
  apply (cancel_epi (resTensorPowIsoSucc f e n).hom).mp
  rw [← Category.assoc]
  rw [resTensorPowIsoSucc_hom]
  have hfirst :
      (resFunctor (MonoidHom.id H)).map
          (resTensorPowMapSucc f e.hom n) =
        resTensorPowMapSucc f e.hom n := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  have hraw := resTensorPowMapSucc_comp
    f (MonoidHom.id H) e.hom e.inv n
  rw [hfirst] at hraw
  have hgroup : f.comp (MonoidHom.id H) = f := by
    ext h
    rfl
  have hcoeff :
      ((resFunctor (MonoidHom.id H)).map e.hom ≫ e.inv).hom.toLinearMap =
        (𝟙 (Rep.res f A) : Rep.res f A ⟶ Rep.res f A).hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom e.hom_inv_id x
  have hnormalized : resTensorPowMapSucc
        (f.comp (MonoidHom.id H))
        ((resFunctor (MonoidHom.id H)).map e.hom ≫ e.inv) n =
      resTensorPowMapSucc f (𝟙 (Rep.res f A)) n := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      exact resTensorPowMapSucc_congr hgroup hcoeff n
  have htensorComp :
      resTensorPowMapSucc f e.hom n ≫
          resTensorPowMapSucc (MonoidHom.id H) e.inv n =
        resTensorPowMapSucc f (𝟙 (Rep.res f A)) n :=
    hraw.symm.trans hnormalized
  rw [htensorComp]
  have he : resTensorPowMapSucc f e.hom n =
      (resTensorPowIsoSucc f e n).hom :=
    (resTensorPowIsoSucc_hom f e n).symm
  have hrefl : resTensorPowMapSucc f
        (𝟙 (Rep.res f A)) n =
      (resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n).hom :=
    (resTensorPowIsoSucc_hom f (Iso.refl (Rep.res f A)) n).symm
  rw [he, hrefl]
  rw [Iso.hom_inv_id, Iso.hom_inv_id]

/-- Let k be a commutative ring and G,H groups in universe u. Let f:H→G and Res=Res_f.
For a G-representation A, write L_n(A)=T_(n+1)(A) for the left-associated positive tensor power
with leading unit k, and R_n(A) for the right-associated power with
R₀(A)=A and R_(n+1)(A)=A⊗R_n(A).
Let σ_n:Res(L_n(A))≅L_n(Res(A)) be the canonical restriction
comparison, and h_A,n:L_(n+1)(A)≅A⊗L_n(A) the head–tail split.
For e:Res(A)≅B, inverse coefficient power comparison followed
by σ_n is T_(n+1)(e⁻¹). -/
theorem resTensorPowIsoSucc_inv_comp_refl_hom
    {A : Rep k G} {B : Rep k H}
    (f : H →* G) (e : Rep.res f A ≅ B) (n : ℕ) :
    (resTensorPowIsoSucc f e n).inv ≫
        (resTensorPowIsoSucc f
          (Iso.refl (Rep.res f A)) n).hom =
      resTensorPowMapSucc (MonoidHom.id H) e.inv n := by
  rw [resTensorPowIsoSucc_inv]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For a commutative ring k and groups G,H,K in universe u, f:H→G, g:K→H,
e:Res_f(A)≅B and ψ:Res_g(B)→C, the inverse restricted power
of e cancels the e part of the composite coefficient power map.
The remaining map is the positive power map induced by g and ψ. -/
theorem resTensorPowIsoSucc_refl_inv_comp_resTensorPowMapSucc
    {K : Type u} [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K}
    (f : H →* G) (g : K →* H)
    (e : Rep.res f A ≅ B) (psi : Rep.res g B ⟶ C)
    (n : ℕ) :
    (resFunctor g).map (resTensorPowIsoSucc f e n).inv ≫
        resTensorPowMapSucc (f.comp g)
          ((resFunctor g).map e.hom ≫ psi) n =
      resTensorPowMapSucc g psi n := by
  rw [resTensorPowMapSucc_comp]
  rw [show resTensorPowMapSucc f e.hom n =
      (resTensorPowIsoSucc f e n).hom by
    exact (resTensorPowIsoSucc_hom f e n).symm]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [Iso.inv_hom_id]
  rw [show (resFunctor g).map
      (𝟙 (TensorPower.tensorPowObj B (n + 1))) = 𝟙 _ by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl]
  rw [Category.id_comp]

end Rep
