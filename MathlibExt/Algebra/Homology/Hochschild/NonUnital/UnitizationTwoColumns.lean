/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationNormalizedCoordinates
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationHochschild
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

public meta import Lean.Elab.Tactic.Omega

/-!
# The original two-column unitization comparison

The raw first-two-column total is the partial total. Its original
even and odd coordinate maps agree with the even ideal word and the word
with the external unit inserted in front. Native partial-total degree
splitting and the original normalized tensor coordinates earn the degree
isomorphisms. The original b, 1-t and -b-prime equations earn the chain law.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex HomologicalComplex₂
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

open ModuleCat.Algebra.Hochschild

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The original bottom raw total has only its original zero-column coordinate. -/
def unitizationRawZeroIso : (cyclicFirstTwoColumns k A).X 0 ≅ chainLevel k A A 0 := by
  let B := cyclicBicomplex k A
  let f := (B.partialTotalMap (Nat.zero_le 1)).f 0
  letI : IsIso f :=
    (B.partialTotalSuccDegreewiseShortExact 0 0).isIso_f_iff.mpr
      (B.totalRow_isZero_X 1 0 (by simp [Nat.add_comm, Nat.add_assoc]))
  exact (asIso f).symm ≪≫
    (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) 0).mapIso
      (cyclicZeroPartialIso k A)

/-- The inverse bottom coordinate is the original retained cell. -/
theorem unitizationRawZeroIso_inv :
    (unitizationRawZeroIso k A).inv =
      cyclicFirstTwoColumnCell k A (0 : Fin 2) 0 0 rfl := by
  simp only [unitizationRawZeroIso, Iso.trans_inv, Iso.symm_inv, asIso_hom,
    Functor.mapIso_inv, HomologicalComplex.eval_map, cyclicZeroPartialIso_inv_f]
  exact (cyclicBicomplex k A).partialTotalComponent_partialTotalMap
    (Nat.zero_le 1) (0 : Fin 1) 0 0 rfl

/-- Native successor splitting retains the original two word coordinates in positive degrees. -/
def unitizationRawPositiveIso (n : ℕ) :
    (cyclicFirstTwoColumns k A).X (n + 1) ≅
      ModuleCat.of k (chainLevel k A A (n + 1) × chainLevel k A A n) :=
  by
    let B := cyclicBicomplex k A
    let α : (B.partialTotal 0).X (n + 1) ≅ chainLevel k A A (n + 1) :=
      (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) (n + 1)).mapIso
        (cyclicZeroPartialIso k A)
    let β : (B.totalRow 1).X (n + 1) ≅ chainLevel k A A n :=
      B.totalRowXIso 1 n (n + 1) (by omega)
    exact B.partialTotalSuccDegreeIso 0 (n + 1) ≪≫ biprod.mapIso α β ≪≫
      ModuleCat.biprodIsoProd (chainLevel k A A (n + 1)) (chainLevel k A A n)

@[reassoc]
theorem product_inl_biprod_inv (X Y : ModuleCat.{max u v} k) :
    ModuleCat.ofHom (LinearMap.inl k X Y) ≫ (ModuleCat.biprodIsoProd X Y).inv = biprod.inl := by
  apply biprod.hom_ext
  · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.inl_fst]
    rfl
  · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inl_snd]
    rfl

@[reassoc]
theorem product_inr_biprod_inv (X Y : ModuleCat.{max u v} k) :
    ModuleCat.ofHom (LinearMap.inr k X Y) ≫ (ModuleCat.biprodIsoProd X Y).inv = biprod.inr := by
  apply biprod.hom_ext
  · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.inr_fst]
    rfl
  · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inr_snd]
    rfl

/-- The inverse even coordinate is precisely the original retained even cell. -/
@[reassoc]
theorem unitizationRawPositiveIso_inv_even (n : ℕ) :
    ModuleCat.ofHom (LinearMap.inl k (chainLevel k A A (n + 1)) (chainLevel k A A n)) ≫
        (unitizationRawPositiveIso k A n).inv =
      cyclicFirstTwoColumnCell k A (0 : Fin 2) (n + 1) (n + 1) (by simp [Nat.add_comm, Nat.add_assoc]) := by
  let B := cyclicBicomplex k A
  let α : (B.partialTotal 0).X (n + 1) ≅ chainLevel k A A (n + 1) :=
    (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) (n + 1)).mapIso
      (cyclicZeroPartialIso k A)
  let β : (B.totalRow 1).X (n + 1) ≅ chainLevel k A A n :=
    B.totalRowXIso 1 n (n + 1) (by omega)
  let γ := ModuleCat.biprodIsoProd (chainLevel k A A (n + 1)) (chainLevel k A A n)
  let P := B.partialTotalSuccDegreeIso 0 (n + 1)
  have hP : biprod.inl ≫ P.inv = (B.partialTotalMap (Nat.zero_le 1)).f (n + 1) := by
    change biprod.inl ≫ biprod.desc ((B.partialTotalMap (Nat.zero_le 1)).f (n + 1))
      (B.partialTotalRowQuotientSectionF 1 (n + 1)) = _
    exact biprod.inl_desc _ _
  change ModuleCat.ofHom (LinearMap.inl k (chainLevel k A A (n + 1)) (chainLevel k A A n)) ≫
    (γ.inv ≫ (biprod.mapIso α β).inv ≫ P.inv) = _
  calc
    _ = biprod.inl ≫ (biprod.mapIso α β).inv ≫ P.inv := by
      rw [← Category.assoc, product_inl_biprod_inv]
    _ = α.inv ≫ biprod.inl ≫ P.inv := by
      rw [biprod.mapIso_inv, biprod.inl_map_assoc]
    _ = α.inv ≫ (B.partialTotalMap (Nat.zero_le 1)).f (n + 1) := by rw [hP]
    _ = _ := by
      change (cyclicZeroPartialIso k A).inv.f (n + 1) ≫
        (B.partialTotalMap (Nat.zero_le 1)).f (n + 1) = _
      rw [cyclicZeroPartialIso_inv_f]
      exact B.partialTotalComponent_partialTotalMap (Nat.zero_le 1)
        (0 : Fin 1) (n + 1) (n + 1) (by simp)

/-- The inverse odd coordinate is precisely the original retained odd cell. -/
@[reassoc]
theorem unitizationRawPositiveIso_inv_odd (n : ℕ) :
    ModuleCat.ofHom (LinearMap.inr k (chainLevel k A A (n + 1)) (chainLevel k A A n)) ≫
        (unitizationRawPositiveIso k A n).inv =
      cyclicFirstTwoColumnCell k A (1 : Fin 2) n (n + 1) (by simp [Nat.add_comm, Nat.add_assoc]) := by
  let B := cyclicBicomplex k A
  let α : (B.partialTotal 0).X (n + 1) ≅ chainLevel k A A (n + 1) :=
    (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) (n + 1)).mapIso
      (cyclicZeroPartialIso k A)
  let β : (B.totalRow 1).X (n + 1) ≅ chainLevel k A A n :=
    B.totalRowXIso 1 n (n + 1) (by omega)
  let γ := ModuleCat.biprodIsoProd (chainLevel k A A (n + 1)) (chainLevel k A A n)
  let P := B.partialTotalSuccDegreeIso 0 (n + 1)
  let c := cyclicFirstTwoColumnCell k A (1 : Fin 2) n (n + 1)
    (by change 1 + n = n + 1; omega)
  have hP : biprod.inr ≫ P.inv = B.partialTotalRowQuotientSectionF 1 (n + 1) := by
    change biprod.inr ≫ biprod.desc ((B.partialTotalMap (Nat.zero_le 1)).f (n + 1))
      (B.partialTotalRowQuotientSectionF 1 (n + 1)) = _
    exact biprod.inr_desc _ _
  have hS : B.partialTotalRowQuotientSectionF 1 (n + 1) = β.hom ≫ c :=
    B.partialTotalRowQuotientSectionF_eq 1 n (n + 1) (by omega)
  change ModuleCat.ofHom (LinearMap.inr k (chainLevel k A A (n + 1)) (chainLevel k A A n)) ≫
    (γ.inv ≫ (biprod.mapIso α β).inv ≫ P.inv) = c
  calc
    _ = biprod.inr ≫ (biprod.mapIso α β).inv ≫ P.inv := by
      rw [← Category.assoc, product_inr_biprod_inv]
    _ = β.inv ≫ biprod.inr ≫ P.inv := by
      rw [biprod.mapIso_inv, biprod.inr_map_assoc]
    _ = (β.inv ≫ B.partialTotalRowQuotientSectionF 1 (n + 1) :
        chainLevel k A A n ⟶ (cyclicFirstTwoColumns k A).X (n + 1)) := by rw [hP]
    _ = c := by rw [hS, Iso.inv_hom_id_assoc]

/-- These retained cells jointly determine a map from the original raw degree. -/
theorem unitizationRawDegree_hom_ext {T : ModuleCat.{max u v} k} (n : ℕ)
    {f g : (cyclicFirstTwoColumns k A).X n ⟶ T}
    (hEven : cyclicFirstTwoColumnCell k A (0 : Fin 2) n n (by simp [Nat.add_comm, Nat.add_assoc]) ≫ f =
      cyclicFirstTwoColumnCell k A (0 : Fin 2) n n (by simp [Nat.add_comm, Nat.add_assoc]) ≫ g)
    (hOdd : ∀ m (hm : n = m + 1),
      cyclicFirstTwoColumnCell k A (1 : Fin 2) m n (by simpa [Nat.add_comm] using hm.symm) ≫ f =
        cyclicFirstTwoColumnCell k A (1 : Fin 2) m n (by simpa [Nat.add_comm] using hm.symm) ≫ g) : f = g := by
  cases n with
  | zero =>
      apply (cancel_epi (unitizationRawZeroIso k A).inv).1
      simpa only [unitizationRawZeroIso_inv] using hEven
  | succ n =>
      apply (cancel_epi (unitizationRawPositiveIso k A n).inv).1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have he := congrArg ModuleCat.Hom.hom hEven
      have ho := congrArg ModuleCat.Hom.hom (hOdd n rfl)
      rw [← unitizationRawPositiveIso_inv_even] at he
      rw [← unitizationRawPositiveIso_inv_odd] at ho
      have he' := DFunLike.congr_fun he x.1
      have ho' := DFunLike.congr_fun ho x.2
      have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he' ho' ⊢
      change f.hom ((unitizationRawPositiveIso k A n).inv.hom (x.1, 0)) =
        g.hom ((unitizationRawPositiveIso k A n).inv.hom (x.1, 0)) at he'
      change f.hom ((unitizationRawPositiveIso k A n).inv.hom (0, x.2)) =
        g.hom ((unitizationRawPositiveIso k A n).inv.hom (0, x.2)) at ho'
      rw [hx, map_add, map_add, map_add]
      exact congrArg₂ (fun a b => a + b) he' ho'

/-- The original raw even retained cell has boundary b into the same column. -/
@[reassoc]
theorem unitizationRawEvenCell_d (n : ℕ) :
    cyclicFirstTwoColumnCell k A (0 : Fin 2) (n + 1) (n + 1) (by simp [Nat.add_comm, Nat.add_assoc]) ≫
        (cyclicFirstTwoColumns k A).d (n + 1) n =
      (bComplex k A).d (n + 1) n ≫
        cyclicFirstTwoColumnCell k A (0 : Fin 2) n n (by simp [Nat.add_comm, Nat.add_assoc]) := by
  let B := cyclicBicomplex k A
  apply (cancel_mono ((cyclicTwoColumnSequence k A).f.f n)).1
  erw [Category.assoc, ← (cyclicTwoColumnSequence k A).f.comm,
    ← Category.assoc, cyclicFirstTwoColumnCell_inclusion,
    total_d, Preadditive.comp_add, ι_D₁, ι_D₂]
  simp only [Fin.val_zero]
  erw [B.d₁_eq_zero (ComplexShape.down ℕ) 0 (n + 1) n
    (by simp [ComplexShape.down_Rel]), zero_add]
  have hd : B.d₂ (ComplexShape.down ℕ) 0 (n + 1) n =
      (bComplex k A).d (n + 1) n ≫ B.ιTotal (ComplexShape.down ℕ) 0 n n (by change 0 + n = n; omega) := by
    rw [B.d₂_eq (ComplexShape.down ℕ) 0
      (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) n (by change 0 + n = n; omega)]
    change (1 : ℤˣ) • _ = _
    exact one_smul _ _
  exact hd.trans (by
    rw [Category.assoc, cyclicFirstTwoColumnCell_inclusion]
    simp only [Fin.val_zero]
    rfl)

/-- The original raw odd retained cell has exactly the source horizontal/vertical signs. -/
@[reassoc]
theorem unitizationRawOddCell_d_succ (n : ℕ) :
    cyclicFirstTwoColumnCell k A (1 : Fin 2) (n + 1) (n + 2)
      (by change 1 + (n + 1) = n + 2; omega) ≫
        (cyclicFirstTwoColumns k A).d (n + 2) (n + 1) =
      (𝟙 _ - cyclicMap k A (n + 1)) ≫
          cyclicFirstTwoColumnCell k A (0 : Fin 2) (n + 1) (n + 1) (by simp [Nat.add_comm, Nat.add_assoc]) -
        ((bPrimeComplex k A).d (n + 1) n ≫
          cyclicFirstTwoColumnCell k A (1 : Fin 2) n (n + 1) (by simp [Nat.add_comm, Nat.add_assoc]) :
            chainLevel k A A (n + 1) ⟶ (cyclicFirstTwoColumns k A).X (n + 1)) := by
  let B := cyclicBicomplex k A
  apply (cancel_mono ((cyclicTwoColumnSequence k A).f.f (n + 1))).1
  erw [Category.assoc, ← (cyclicTwoColumnSequence k A).f.comm,
    ← Category.assoc, cyclicFirstTwoColumnCell_inclusion,
    total_d, Preadditive.comp_add, ι_D₁, ι_D₂]
  simp only [Fin.val_one]
  have hH : B.d₁ (ComplexShape.down ℕ) 1 (n + 1) (n + 1) =
      (𝟙 _ - cyclicMap k A (n + 1)) ≫
        B.ιTotal (ComplexShape.down ℕ) 0 (n + 1) (n + 1)
          (by change 0 + (n + 1) = n + 1; omega) := by
    rw [B.d₁_eq (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (n + 1) (n + 1)
      (by change 0 + (n + 1) = n + 1; omega)]
    change (1 : ℤˣ) • (((B.d 1 0).f (n + 1)) ≫ _) = _
    rw [one_smul, cyclicBicomplex_horizontal, ite_eq_left (show Even (0 : ℕ) from ⟨0, rfl⟩)]
    rfl
  let d' : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bPrimeComplex k A).d (n + 1) n
  have hV : B.d₂ (ComplexShape.down ℕ) 1 (n + 1) (n + 1) =
      -(d' ≫ B.ιTotal (ComplexShape.down ℕ) 1 n (n + 1) (by change 1 + n = n + 1; omega)) := by
    rw [B.d₂_eq (ComplexShape.down ℕ) 1
      (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) (n + 1)
      (by change 1 + n = n + 1; omega)]
    have hv : (((B.X 1).d (n + 1) n) :
        chainLevel k A A (n + 1) ⟶ chainLevel k A A n) = d' :=
      (cyclicBicomplex_vertical k A 1 n).trans
        (ite_eq_right (show ¬Even (1 : ℕ) by decide))
    let ι : chainLevel k A A n ⟶ (cyclicTotal k A).X (n + 1) :=
      B.ιTotal (ComplexShape.down ℕ) 1 n (n + 1) (by change 1 + n = n + 1; omega)
    change (-1 : ℤˣ) • (((B.X 1).d (n + 1) n) ≫ ι) = -(d' ≫ ι)
    exact (congrArg (fun f : chainLevel k A A (n + 1) ⟶ chainLevel k A A n =>
      (-1 : ℤˣ) • (f ≫ ι)) hv).trans (by rw [Units.neg_smul, one_smul])
  rw [hH, hV]
  let t : chainLevel k A A (n + 1) ⟶ chainLevel k A A (n + 1) :=
    𝟙 _ - cyclicMap k A (n + 1)
  let ι₀ : chainLevel k A A (n + 1) ⟶ (cyclicTotal k A).X (n + 1) :=
    B.ιTotal (ComplexShape.down ℕ) 0 (n + 1) (n + 1)
      (by change 0 + (n + 1) = n + 1; omega)
  let ι₁ : chainLevel k A A n ⟶ (cyclicTotal k A).X (n + 1) :=
    B.ιTotal (ComplexShape.down ℕ) 1 n (n + 1) (by change 1 + n = n + 1; omega)
  let e₀ := cyclicFirstTwoColumnCell k A (0 : Fin 2) (n + 1) (n + 1) (by simp)
  let e₁ := cyclicFirstTwoColumnCell k A (1 : Fin 2) n (n + 1)
    (by change 1 + n = n + 1; omega)
  let ι : (cyclicFirstTwoColumns k A).X (n + 1) ⟶ (cyclicTotal k A).X (n + 1) :=
    (cyclicTwoColumnSequence k A).f.f (n + 1)
  have he₀ : e₀ ≫ ι = ι₀ := by
    simpa only [Fin.val_zero] using
      (cyclicFirstTwoColumnCell_inclusion k A (0 : Fin 2) (n + 1) (n + 1) (by simp))
  have he₁ : e₁ ≫ ι = ι₁ := by
    simpa only [Fin.val_one] using
      (cyclicFirstTwoColumnCell_inclusion k A (1 : Fin 2) n (n + 1)
        (by change 1 + n = n + 1; omega))
  change t ≫ ι₀ + -(d' ≫ ι₁) = (t ≫ e₀ - d' ≫ e₁) ≫ ι
  conv_rhs => rw [Preadditive.sub_comp, Category.assoc, he₀, Category.assoc, he₁]
  exact (sub_eq_add_neg (t ≫ ι₀) (d' ≫ ι₁)).symm

/-- The bottom odd boundary is zero because its original 1-t₀ is zero. -/
@[reassoc]
theorem unitizationRawOddCell_d_zero :
    cyclicFirstTwoColumnCell k A (1 : Fin 2) 0 1 (by simp [Nat.add_comm, Nat.add_assoc]) ≫
        (cyclicFirstTwoColumns k A).d 1 0 = 0 := by
  let B := cyclicBicomplex k A
  apply (cancel_mono ((cyclicTwoColumnSequence k A).f.f 0)).1
  erw [Category.assoc, ← (cyclicTwoColumnSequence k A).f.comm,
    ← Category.assoc, cyclicFirstTwoColumnCell_inclusion,
    total_d, Preadditive.comp_add, ι_D₁, ι_D₂]
  simp only [Fin.val_one]
  erw [B.d₂_eq_zero (ComplexShape.down ℕ) 1 0 0
    (by simp [ComplexShape.down_Rel]), add_zero]
  have hH := cyclicBicomplex_d₁ k A 0 0
  simp only [show Even (0 : ℕ) from ⟨0, rfl⟩, ite_eq_left, Nat.zero_add] at hH
  erw [hH]
  change (𝟙 _ - ModuleCat.ofHom (TensorPower.consCyclicOperator k A 0)) ≫ _ = 0 ≫ _
  rw [TensorPower.consCyclicOperator_zero]
  have hId : ModuleCat.ofHom (1 : chainLevel k A A 0 →ₗ[k] chainLevel k A A 0) =
      𝟙 (chainLevel k A A 0) := rfl
  rw [hId, sub_self, zero_comp, zero_comp]

/-- Every comparison component is from the native original coordinate isomorphisms. -/
def unitizationTwoColumnCoordinateIso (n : ℕ) :
    (cyclicFirstTwoColumns k A).X n ≅ (unitizationReducedNormalizedComplex k A).X n :=
  match n with
  | 0 => unitizationRawZeroIso k A ≪≫ (unitizationReducedZeroIso k A).symm
  | n + 1 => unitizationRawPositiveIso k A n ≪≫
      (unitizationNormalizedPositiveEquiv k A n).toModuleIso.symm ≪≫
      (unitizationReducedPositiveIso k A n).symm

/-- The complete even comparison is the original ideal word in the original normalized quotient. -/
@[reassoc]
theorem unitizationTwoColumnCoordinateIso_even (n : ℕ) :
    cyclicFirstTwoColumnCell k A (0 : Fin 2) n n (by simp [Nat.add_comm, Nat.add_assoc]) ≫
        (unitizationTwoColumnCoordinateIso k A n).hom ≫
        (kernel.ι (unitizationNormalizedScalarProjector k A)).f n =
      unitizationEvenWord k A n := by
  cases n with
  | zero =>
      change cyclicFirstTwoColumnCell k A (0 : Fin 2) 0 0 _ ≫
        ((unitizationRawZeroIso k A).hom ≫ (unitizationReducedZeroIso k A).inv) ≫
          (kernel.ι (unitizationNormalizedScalarProjector k A)).f 0 = _
      rw [← unitizationRawZeroIso_inv]
      simp only [Category.assoc, Iso.inv_hom_id_assoc,
        unitizationReducedZeroIso_inv_inclusion]
  | succ n =>
      change cyclicFirstTwoColumnCell k A (0 : Fin 2) (n + 1) (n + 1) _ ≫
        ((unitizationRawPositiveIso k A n).hom ≫
          ((unitizationNormalizedPositiveEquiv k A n).toModuleIso.inv ≫
            (unitizationReducedPositiveIso k A n).inv)) ≫
          (kernel.ι (unitizationNormalizedScalarProjector k A)).f (n + 1) = _
      rw [← unitizationRawPositiveIso_inv_even]
      simp only [Category.assoc, Iso.inv_hom_id_assoc,
        unitizationReducedPositiveIso, asIso_inv, IsIso.inv_hom_id, Category.comp_id]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (unitizationNormalizedPositiveEquiv k A n).injective
      exact ((unitizationNormalizedPositiveEquiv k A n).apply_symm_apply (x, 0)).trans
        (unitizationNormalizedPositiveEquiv_even k A n x).symm

/-- The complete odd comparison is the external unit followed by the original ideal word. -/
@[reassoc]
theorem unitizationTwoColumnCoordinateIso_odd (n : ℕ) :
    cyclicFirstTwoColumnCell k A (1 : Fin 2) n (n + 1) (by simp [Nat.add_comm, Nat.add_assoc]) ≫
        (unitizationTwoColumnCoordinateIso k A (n + 1)).hom ≫
        (kernel.ι (unitizationNormalizedScalarProjector k A)).f (n + 1) =
      unitizationOddWord k A n := by
  change cyclicFirstTwoColumnCell k A (1 : Fin 2) n (n + 1) _ ≫
    ((unitizationRawPositiveIso k A n).hom ≫
      ((unitizationNormalizedPositiveEquiv k A n).toModuleIso.inv ≫
        (unitizationReducedPositiveIso k A n).inv)) ≫
      (kernel.ι (unitizationNormalizedScalarProjector k A)).f (n + 1) = _
  rw [← unitizationRawPositiveIso_inv_odd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    unitizationReducedPositiveIso, asIso_inv, IsIso.inv_hom_id, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (unitizationNormalizedPositiveEquiv k A n).injective
  exact ((unitizationNormalizedPositiveEquiv k A n).apply_symm_apply (0, x)).trans
    (unitizationNormalizedPositiveEquiv_odd k A n x).symm

/-- The original two retained raw columns are the reduced normalized unitization complex. -/
def unitizationTwoColumnIso :
    cyclicFirstTwoColumns k A ≅ unitizationReducedNormalizedComplex k A :=
  HomologicalComplex.Hom.isoOfComponents (unitizationTwoColumnCoordinateIso k A)
    (fun i j hij => by
      have h : j + 1 = i := hij
      subst i
      apply (cancel_mono ((kernel.ι (unitizationNormalizedScalarProjector k A)).f j)).1
      have hJ := (kernel.ι (unitizationNormalizedScalarProjector k A)).comm (j + 1) j
      simp only [Category.assoc, ← hJ]
      apply unitizationRawDegree_hom_ext k A (j + 1)
      · change (cyclicFirstTwoColumnCell k A (0 : Fin 2) (j + 1) (j + 1) _ ≫
          (unitizationTwoColumnCoordinateIso k A (j + 1)).hom ≫
          (kernel.ι (unitizationNormalizedScalarProjector k A)).f (j + 1)) ≫
            (normalizedBComplex k (Unitization k A)).d (j + 1) j = _
        rw [unitizationTwoColumnCoordinateIso_even, unitizationEvenWord_d, unitizationRawEvenCell_d_assoc,
          unitizationTwoColumnCoordinateIso_even]
      · intro m hm
        have hm' : j = m := by omega
        subst m
        cases j with
        | zero =>
            change (cyclicFirstTwoColumnCell k A (1 : Fin 2) 0 1 _ ≫
              (unitizationTwoColumnCoordinateIso k A 1).hom ≫
              (kernel.ι (unitizationNormalizedScalarProjector k A)).f 1) ≫
                (normalizedBComplex k (Unitization k A)).d 1 0 = _
            rw [unitizationTwoColumnCoordinateIso_odd, unitizationOddWord_d_zero]
            erw [unitizationRawOddCell_d_zero_assoc k A, zero_comp]
        | succ n =>
            change (cyclicFirstTwoColumnCell k A (1 : Fin 2) (n + 1) (n + 2) _ ≫
              (unitizationTwoColumnCoordinateIso k A (n + 2)).hom ≫
              (kernel.ι (unitizationNormalizedScalarProjector k A)).f (n + 2)) ≫
                (normalizedBComplex k (Unitization k A)).d (n + 2) (n + 1) = _
            rw [unitizationTwoColumnCoordinateIso_odd, unitizationOddWord_d_succ]
            erw [unitizationRawOddCell_d_succ_assoc k A n]
            simp only [Preadditive.sub_comp, Category.assoc,
              unitizationTwoColumnCoordinateIso_even,
              unitizationTwoColumnCoordinateIso_odd]
            erw [Category.assoc
              ((bPrimeComplex k A).d (n + 1) n : chainLevel k A A (n + 1) ⟶ chainLevel k A A n),
              unitizationTwoColumnCoordinateIso_odd]
            rfl)

/-- The chain comparison retains each exact original coordinate, rather than a chosen equivalence field. -/
@[simp]
theorem unitizationTwoColumnIso_hom_f (n : ℕ) :
    (unitizationTwoColumnIso k A).hom.f n = (unitizationTwoColumnCoordinateIso k A n).hom := rfl

/-- The source-defined nonunital HH is from its original first-two-column total. -/
def unitizationHochschildTwoColumnIso (n : ℕ) :
    unitizationHochschildHomology k A n ≅ (cyclicFirstTwoColumns k A).homology n :=
  unitizationHochschildReducedNormalizedIso k A n ≪≫
    (homologyFunctor (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n).mapIso
      (unitizationTwoColumnIso k A).symm

end ModuleCat.Algebra.Hochschild.NonUnital
