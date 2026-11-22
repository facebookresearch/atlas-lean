/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.TensorPowers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Tensor-word monoids and their generator maps

In a monoidal category with coproducts indexed by `ℕ` and `Σ _ : ℕ, ℕ`,
the coproduct `∐ n, tensorPowObj X n` becomes a monoid object using the
finite-power concatenation isomorphisms. Tensoring on either side must
preserve the stated `Discrete ℕ` colimits, and tensoring on the right
must also preserve the stated pair-index colimits. These hypotheses give
associativity without a triple-index coproduct assumption.

The construction is functorial in `X`. Degree-one inclusion determines a
natural equivalence `tensorWordHomEquiv` between maps from `X` to a monoid's
carrier and monoid morphisms from the tensor-word monoid, with the generator
computation and uniqueness laws.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace CategoryTheory.MonoidalCategory.TensorWord

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [∀ (f : ℕ → C), HasCoproduct f]
variable [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
variable [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
variable [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
variable [∀ (T : C),
  PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)]

/-- Coproduct of finite tensor powers (`abbrev` so preservation-epi
unification sees through it). -/
noncomputable abbrev tensorWordObj (X : C) : C :=
  ∐ fun n : ℕ => tensorPowObj X n

/-- Inclusion of the `n`-th power. -/
noncomputable def tensorWordι (X : C) (n : ℕ) :
    tensorPowObj X n ⟶ tensorWordObj X :=
  Limits.Sigma.ι (fun n : ℕ => tensorPowObj X n) n

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- `Sigma.desc` evaluates on `tensorWordι` to the corresponding component. -/
@[simp]
theorem tensorWordι_desc (X : C) {P : C}
    (p : ∀ n : ℕ, tensorPowObj X n ⟶ P) (n : ℕ) :
    tensorWordι X n ≫ Limits.Sigma.desc p = p n :=
  Limits.Sigma.ι_comp_desc p n

/-- Functorial map on carriers via `tensorPowMap`. -/
noncomputable def tensorWordMap {X Y : C} (f : X ⟶ Y) :
    tensorWordObj X ⟶ tensorWordObj Y :=
  Limits.Sigma.map (fun n : ℕ => tensorPowMap f n)

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Functorial map commutes with the degree inclusions. -/
@[simp]
theorem tensorWordMap_ι {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorWordι X n ≫ tensorWordMap f =
      tensorPowMap f n ≫ tensorWordι Y n := by
  unfold tensorWordι tensorWordMap
  exact Limits.Sigma.ι_map (fun n : ℕ => tensorPowMap f n) n

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Functorial map preserves identities. -/
@[simp]
theorem tensorWordMap_id (X : C) :
    tensorWordMap (𝟙 X) = 𝟙 (tensorWordObj X) := by
  unfold tensorWordMap tensorWordObj
  have h : (fun n : ℕ => tensorPowMap (𝟙 X) n) = (fun _ : ℕ => 𝟙 _) := by
    funext n
    exact tensorPowMap_id X n
  rw [h]
  exact Limits.Sigma.map_id

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Functorial map preserves composition. -/
theorem tensorWordMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorWordMap f ≫ tensorWordMap g = tensorWordMap (f ≫ g) := by
  unfold tensorWordMap tensorWordObj
  rw [Limits.Sigma.map_comp_map]
  congr 1
  funext n
  exact (tensorPowMap_comp f g n).symm

/-- Unit via degree-zero inclusion (`pow 0 = 𝟙` definitionally). -/
noncomputable def tensorWordOne (X : C) : 𝟙_ C ⟶ tensorWordObj X :=
  Limits.Sigma.ι (fun n : ℕ => tensorPowObj X n) 0

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Morphisms out of `tensorWordObj X ⊗ tensorWordObj X` are determined on
pairs of injections (two-level epi, following `copowerTensor_hom_ext`). -/
theorem tensorWord_hom_ext {X : C} {P : C}
    {f g : tensorWordObj X ⊗ tensorWordObj X ⟶ P}
    (h : ∀ n m,
      (tensorWordι X n ⊗ₘ tensorWordι X m) ≫ f =
        (tensorWordι X n ⊗ₘ tensorWordι X m) ≫ g) :
    f = g := by
  apply (cancel_epi
    (preservesColimitIso (tensorRight (tensorWordObj X))
      (Discrete.functor (fun n : ℕ => tensorPowObj X n))).inv).mp
  apply colimit.hom_ext
  rintro ⟨n⟩
  simp only [ι_preservesColimitIso_inv_assoc]
  apply (cancel_epi
    (preservesColimitIso (tensorLeft (tensorPowObj X n))
      (Discrete.functor (fun m : ℕ => tensorPowObj X m))).inv).mp
  apply colimit.hom_ext
  rintro ⟨m⟩
  simp only [ι_preservesColimitIso_inv_assoc]
  change (tensorPowObj X n ◁ tensorWordι X m) ≫
    (tensorWordι X n ▷ tensorWordObj X) ≫ f =
      (tensorPowObj X n ◁ tensorWordι X m) ≫
        (tensorWordι X n ▷ tensorWordObj X) ≫ g
  simpa only [MonoidalCategory.tensorHom_def', Category.assoc] using h n m

/-- Forward comparison map of the distribution iso (desc-based, following
`copowerTensorComparison`; no `Sigma.map`, so no `HasCoproductsOfShape`). -/
noncomputable def tensorWordComparison (X : C) :
    (tensorWordObj X ⊗ tensorWordObj X) ⟶
      ∐ fun p : Σ _ : ℕ, ℕ =>
        tensorPowObj X p.1 ⊗ tensorPowObj X p.2 :=
  (preservesColimitIso (tensorRight (tensorWordObj X))
      (Discrete.functor (fun n : ℕ => tensorPowObj X n))).hom ≫
    (Limits.Sigma.isoColimit
      ((Discrete.functor (fun n : ℕ => tensorPowObj X n)) ⋙
        tensorRight (tensorWordObj X))).inv ≫
    Limits.Sigma.desc (fun n : ℕ =>
      (preservesColimitIso (tensorLeft (tensorPowObj X n))
          (Discrete.functor (fun m : ℕ => tensorPowObj X m))).hom ≫
        (Limits.Sigma.isoColimit
          ((Discrete.functor (fun m : ℕ => tensorPowObj X m)) ⋙
            tensorLeft (tensorPowObj X n))).inv ≫
        Limits.Sigma.desc (fun m : ℕ =>
          Limits.Sigma.ι (fun p : Σ _ : ℕ, ℕ =>
            tensorPowObj X p.1 ⊗ tensorPowObj X p.2)
            (⟨n, m⟩ : Σ _ : ℕ, ℕ)))

/-- Backward map of the distribution iso (plain `desc` of tensor pairs). -/
noncomputable def tensorWordDistribInv (X : C) :
    (∐ fun p : Σ _ : ℕ, ℕ =>
        tensorPowObj X p.1 ⊗ tensorPowObj X p.2) ⟶
      (tensorWordObj X ⊗ tensorWordObj X) :=
  Limits.Sigma.desc (fun p : Σ _ : ℕ, ℕ =>
    tensorWordι X p.1 ⊗ₘ tensorWordι X p.2)

omit [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
@[reassoc (attr := simp)]
private theorem tensorWordComparison_ι (X : C) (n m : ℕ) :
    (tensorWordι X n ⊗ₘ tensorWordι X m) ≫ tensorWordComparison X =
      Limits.Sigma.ι (fun p : Σ _ : ℕ, ℕ =>
        tensorPowObj X p.1 ⊗ tensorPowObj X p.2) (⟨n, m⟩ : Σ _ : ℕ, ℕ) := by
  rw [MonoidalCategory.tensorHom_def']
  rw [Category.assoc]
  change (tensorPowObj X n ◁ tensorWordι X m) ≫
    (tensorRight (tensorWordObj X)).map (tensorWordι X n) ≫
      tensorWordComparison X = _
  unfold tensorWordComparison tensorWordι
  rw [ι_preservesColimitIso_hom_assoc]
  rw [Limits.Sigma.ι_isoColimit_inv_assoc]
  rw [Limits.Sigma.ι_comp_desc]
  change (tensorLeft (tensorPowObj X n)).map
      (Limits.Sigma.ι (fun m : ℕ => tensorPowObj X m) m) ≫ _ = _
  rw [ι_preservesColimitIso_hom_assoc]
  rw [Limits.Sigma.ι_isoColimit_inv_assoc]
  rw [Limits.Sigma.ι_comp_desc]

/-- The single distribution/comparison iso, packaging the forward and
backward maps. All transport goes through this iso. -/
noncomputable def tensorWordDistrib (X : C) :
    (tensorWordObj X ⊗ tensorWordObj X) ≅
      ∐ fun p : Σ _ : ℕ, ℕ =>
        tensorPowObj X p.1 ⊗ tensorPowObj X p.2 where
  hom := tensorWordComparison X
  inv := tensorWordDistribInv X
  hom_inv_id := by
    apply tensorWord_hom_ext
    intro n m
    rw [← Category.assoc, tensorWordComparison_ι, Category.comp_id]
    unfold tensorWordDistribInv tensorWordι
    exact Limits.Sigma.ι_comp_desc _ (⟨n, m⟩ : Σ _ : ℕ, ℕ)
  inv_hom_id := by
    apply Limits.Sigma.hom_ext
    intro p
    obtain ⟨n, m⟩ := p
    rw [← Category.assoc]
    unfold tensorWordDistribInv tensorWordι
    rw [Limits.Sigma.ι_comp_desc, Category.comp_id]
    exact tensorWordComparison_ι X n m

omit [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
@[simp]
private theorem tensorWordDistrib_ι (X : C) (n m : ℕ) :
    (tensorWordι X n ⊗ₘ tensorWordι X m) ≫ (tensorWordDistrib X).hom =
      Limits.Sigma.ι (fun p : Σ _ : ℕ, ℕ =>
        tensorPowObj X p.1 ⊗ tensorPowObj X p.2) (⟨n, m⟩ : Σ _ : ℕ, ℕ) :=
  tensorWordComparison_ι X n m

/-- Multiplication induced by `tensorPowObj_add` after distribution. -/
noncomputable def tensorWordMul (X : C) :
    tensorWordObj X ⊗ tensorWordObj X ⟶ tensorWordObj X :=
  (tensorWordDistrib X).hom ≫
    Limits.Sigma.desc (fun p : Σ _ : ℕ, ℕ =>
      (tensorPowObj_add X p.1 p.2).inv ≫ tensorWordι X (p.1 + p.2))

omit [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Multiplication computes on injections via `tensorPowObj_add`. -/
@[simp]
theorem tensorWordMul_ι (X : C) (n m : ℕ) :
    (tensorWordι X n ⊗ₘ tensorWordι X m) ≫ tensorWordMul X =
      (tensorPowObj_add X n m).inv ≫ tensorWordι X (n + m) := by
  unfold tensorWordMul
  rw [← Category.assoc, tensorWordDistrib_ι]
  unfold tensorWordι
  exact Limits.Sigma.ι_comp_desc _ (⟨n, m⟩ : Σ _ : ℕ, ℕ)

omit [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Inverse direction: the sigma injection pulls back through `distrib.inv`
to the corresponding tensor of injections. -/
private theorem tensorWordDistrib_inv_ι (X : C) (n m : ℕ) :
    Limits.Sigma.ι (fun p : Σ _ : ℕ, ℕ =>
        tensorPowObj X p.1 ⊗ tensorPowObj X p.2)
        (⟨n, m⟩ : Σ _ : ℕ, ℕ) ≫ (tensorWordDistrib X).inv =
      (tensorWordι X n ⊗ₘ tensorWordι X m) := by
  have h := tensorWordDistrib_ι X n m
  calc Limits.Sigma.ι _ (⟨n, m⟩ : Σ _ : ℕ, ℕ) ≫ (tensorWordDistrib X).inv
      = ((tensorWordι X n ⊗ₘ tensorWordι X m) ≫
          (tensorWordDistrib X).hom) ≫ (tensorWordDistrib X).inv := by
        rw [h]
    _ = (tensorWordι X n ⊗ₘ tensorWordι X m) ≫
          ((tensorWordDistrib X).hom ≫ (tensorWordDistrib X).inv) := by
        rw [Category.assoc]
    _ = (tensorWordι X n ⊗ₘ tensorWordι X m) := by
        rw [Iso.hom_inv_id, Category.comp_id]

omit [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Left-unit law via `tensorPowObj_add_zero_left`. -/
theorem tensorWordOneMul (X : C) :
    tensorWordOne X ▷ tensorWordObj X ≫ tensorWordMul X =
      (λ_ (tensorWordObj X)).hom := by
  apply (cancel_epi
    (preservesColimitIso (tensorLeft (𝟙_ C))
      (Discrete.functor (fun m : ℕ => tensorPowObj X m))).inv).mp
  apply colimit.hom_ext
  rintro ⟨m⟩
  simp only [ι_preservesColimitIso_inv_assoc]
  have hmul : (tensorWordOne X ⊗ₘ tensorWordι X m) ≫ tensorWordMul X =
      (tensorLeft (𝟙_ C)).map (tensorWordι X m) ≫
        (λ_ (tensorWordObj X)).hom := by
    have hmulι : ((tensorWordι X 0 ⊗ₘ tensorWordι X m) ≫ tensorWordMul X) =
        (tensorPowObj_add X 0 m).inv ≫ tensorWordι X (0 + m) :=
      tensorWordMul_ι X 0 m
    have hbase : (tensorWordOne X ⊗ₘ tensorWordι X m) ≫ tensorWordMul X =
        ((tensorWordι X 0 ⊗ₘ tensorWordι X m) ≫ tensorWordMul X) := rfl
    rw [hbase, hmulι]
    have hNat : (𝟙_ C ◁ tensorWordι X m) ≫ (λ_ (tensorWordObj X)).hom =
        (λ_ (tensorPowObj X m)).hom ≫ tensorWordι X m :=
      leftUnitor_naturality (tensorWordι X m)
    have hmap : (tensorLeft (𝟙_ C)).map (tensorWordι X m) =
        (𝟙_ C ◁ tensorWordι X m) := rfl
    rw [hmap, hNat]
    have hAdd := tensorPowObj_add_zero_left X m
    have step2a : (tensorPowObj_add X 0 m).inv ≫
        eqToHom (congrArg (tensorPowObj X) (Nat.zero_add m)) =
        (λ_ (tensorPowObj X m)).hom := by
      apply (cancel_epi (tensorPowObj_add X 0 m).hom).mp
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      exact hAdd.symm
    have step1 : (tensorPowObj_add X 0 m).inv ≫ tensorWordι X (0 + m) =
        (tensorPowObj_add X 0 m).inv ≫ (eqToHom (congrArg (tensorPowObj X)
          (Nat.zero_add m)) ≫ tensorWordι X m) := by
      congr 1
      unfold tensorWordι
      have h := Limits.Sigma.eqToHom_comp_ι
        (fun n : ℕ => tensorPowObj X n) (Nat.zero_add m)
      exact ((CategoryTheory.eqToHom_comp_iff _ _ _).mpr h.symm).symm
    exact step1.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ tensorWordι X m) step2a))
  rw [MonoidalCategory.tensorHom_def', Category.assoc] at hmul
  exact hmul

omit [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Right-unit law via `tensorPowObj_add_zero_right`. -/
theorem tensorWordMulOne (X : C) :
    tensorWordObj X ◁ tensorWordOne X ≫ tensorWordMul X =
      (ρ_ (tensorWordObj X)).hom := by
  apply (cancel_epi
    (preservesColimitIso (tensorRight (𝟙_ C))
      (Discrete.functor (fun n : ℕ => tensorPowObj X n))).inv).mp
  apply colimit.hom_ext
  rintro ⟨n⟩
  simp only [ι_preservesColimitIso_inv_assoc]
  have hmul : (tensorWordι X n ⊗ₘ tensorWordOne X) ≫ tensorWordMul X =
      (tensorRight (𝟙_ C)).map (tensorWordι X n) ≫
        (ρ_ (tensorWordObj X)).hom := by
    have hmulι : ((tensorWordι X n ⊗ₘ tensorWordι X 0) ≫ tensorWordMul X) =
        (tensorPowObj_add X n 0).inv ≫ tensorWordι X (n + 0) :=
      tensorWordMul_ι X n 0
    have hbase : (tensorWordι X n ⊗ₘ tensorWordOne X) ≫ tensorWordMul X =
        ((tensorWordι X n ⊗ₘ tensorWordι X 0) ≫ tensorWordMul X) := rfl
    rw [hbase, hmulι]
    have hNat : (tensorWordι X n ▷ 𝟙_ C) ≫ (ρ_ (tensorWordObj X)).hom =
        (ρ_ (tensorPowObj X n)).hom ≫ tensorWordι X n :=
      rightUnitor_naturality (tensorWordι X n)
    have hmap : (tensorRight (𝟙_ C)).map (tensorWordι X n) =
        (tensorWordι X n ▷ 𝟙_ C) := rfl
    rw [hmap, hNat]
    have hAdd := tensorPowObj_add_zero_right X n
    have step2a : (tensorPowObj_add X n 0).inv ≫
        eqToHom (congrArg (tensorPowObj X) (Nat.add_zero n)) =
        (ρ_ (tensorPowObj X n)).hom := by
      apply (cancel_epi (tensorPowObj_add X n 0).hom).mp
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      simp [hAdd]
    have step1 : (tensorPowObj_add X n 0).inv ≫ tensorWordι X (n + 0) =
        (tensorPowObj_add X n 0).inv ≫ (eqToHom (congrArg (tensorPowObj X)
          (Nat.add_zero n)) ≫ tensorWordι X n) := by
      congr 1
      unfold tensorWordι
      have h := Limits.Sigma.eqToHom_comp_ι
        (fun n : ℕ => tensorPowObj X n) (Nat.add_zero n)
      exact ((CategoryTheory.eqToHom_comp_iff _ _ _).mpr h.symm).symm
    exact step1.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ tensorWordι X n) step2a))
  rw [MonoidalCategory.tensorHom_def, Category.assoc] at hmul
  exact hmul

/-- Morphisms out of `(tensorWordObj X ⊗ tensorWordObj X) ⊗ tensorWordObj X`
are determined on triple tensor injections (three-level epi via the
distribution iso and preservation; uses the `Discrete (Σ _ : ℕ, ℕ)`
preservation hypothesis). -/
theorem tensorWord_hom_ext_triple {X : C} {P : C}
    {f g : (tensorWordObj X ⊗ tensorWordObj X) ⊗ tensorWordObj X ⟶ P}
    (h : ∀ l m k,
      ((tensorWordι X l ⊗ₘ tensorWordι X m) ⊗ₘ tensorWordι X k) ≫ f =
        ((tensorWordι X l ⊗ₘ tensorWordι X m) ⊗ₘ tensorWordι X k) ≫ g) :
    f = g := by
  have hEinv : (tensorIso (tensorWordDistrib X)
        (Iso.refl (tensorWordObj X))).inv =
      (tensorWordDistrib X).inv ⊗ₘ 𝟙 (tensorWordObj X) := rfl
  apply (cancel_epi (tensorIso (tensorWordDistrib X)
    (Iso.refl (tensorWordObj X))).inv).mp
  apply (cancel_epi
    (preservesColimitIso (tensorRight (tensorWordObj X))
      (Discrete.functor (fun p : Σ _ : ℕ, ℕ =>
        tensorPowObj X p.1 ⊗ tensorPowObj X p.2))).inv).mp
  apply colimit.hom_ext
  rintro ⟨⟨n, m⟩⟩
  simp only [ι_preservesColimitIso_inv_assoc]
  have hprefix : (Limits.Sigma.ι (fun p : Σ _ : ℕ, ℕ =>
          tensorPowObj X p.1 ⊗ tensorPowObj X p.2)
          (⟨n, m⟩ : Σ _ : ℕ, ℕ) ▷ tensorWordObj X) ≫
        (tensorIso (tensorWordDistrib X)
          (Iso.refl (tensorWordObj X))).inv =
        ((tensorWordι X n ⊗ₘ tensorWordι X m) ⊗ₘ
          𝟙 (tensorWordObj X)) := by
    rw [hEinv, MonoidalCategory.tensorHom_def, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight, tensorWordDistrib_inv_ι]
    exact (MonoidalCategory.tensorHom_def _ _).symm
  change ((Limits.Sigma.ι (fun p : Σ _ : ℕ, ℕ =>
      tensorPowObj X p.1 ⊗ tensorPowObj X p.2)
      (⟨n, m⟩ : Σ _ : ℕ, ℕ) ▷ tensorWordObj X) ≫
      (tensorIso (tensorWordDistrib X)
        (Iso.refl (tensorWordObj X))).inv ≫ f) =
    ((Limits.Sigma.ι (fun p : Σ _ : ℕ, ℕ =>
      tensorPowObj X p.1 ⊗ tensorPowObj X p.2)
      (⟨n, m⟩ : Σ _ : ℕ, ℕ) ▷ tensorWordObj X) ≫
      (tensorIso (tensorWordDistrib X)
        (Iso.refl (tensorWordObj X))).inv ≫ g)
  simp only [← Category.assoc, hprefix]
  apply (cancel_epi
    (preservesColimitIso
      (tensorLeft (tensorPowObj X n ⊗ tensorPowObj X m))
      (Discrete.functor (fun k : ℕ => tensorPowObj X k))).inv).mp
  apply colimit.hom_ext
  rintro ⟨k⟩
  simp only [ι_preservesColimitIso_inv_assoc]
  have hprefix2 : ((tensorPowObj X n ⊗ tensorPowObj X m) ◁
        tensorWordι X k) ≫
        ((tensorWordι X n ⊗ₘ tensorWordι X m) ⊗ₘ
          𝟙 (tensorWordObj X)) =
        ((tensorWordι X n ⊗ₘ tensorWordι X m) ⊗ₘ
          tensorWordι X k) := by
    have hW : ((tensorWordObj X ⊗ tensorWordObj X) ◁
          𝟙 (tensorWordObj X)) = 𝟙 _ := Functor.map_id
      (tensorLeft (tensorWordObj X ⊗ tensorWordObj X)) (tensorWordObj X)
    rw [MonoidalCategory.tensorHom_def, ← Category.assoc,
      ← MonoidalCategory.tensorHom_def', hW, Category.comp_id]
  change (((tensorPowObj X n ⊗ tensorPowObj X m) ◁ tensorWordι X k) ≫
      ((tensorWordι X n ⊗ₘ tensorWordι X m) ⊗ₘ
        𝟙 (tensorWordObj X)) ≫ f) =
    (((tensorPowObj X n ⊗ tensorPowObj X m) ◁ tensorWordι X k) ≫
      ((tensorWordι X n ⊗ₘ tensorWordι X m) ⊗ₘ
        𝟙 (tensorWordObj X)) ≫ g)
  simp only [← Category.assoc, hprefix2]
  exact h n m k

omit [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Left-associated component of associativity: two multiplications on the
left reduce to the reassociated `tensorPowObj_add` inverse pair. -/
private theorem tensorWordMulAssoc_left (X : C) (l m k : ℕ) :
    ((tensorWordι X l ⊗ₘ tensorWordι X m) ⊗ₘ tensorWordι X k) ≫
      (tensorWordMul X ▷ tensorWordObj X ≫ tensorWordMul X) =
      ((((tensorPowObj_add X l m).inv ⊗ₘ 𝟙 (tensorPowObj X k)) ≫
        (tensorPowObj_add X (l+m) k).inv) ≫
        tensorWordι X ((l+m)+k)) := by
  rw [← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id,
    tensorWordMul_ι X l m, ← Category.id_comp (tensorWordι X k),
    ← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    tensorWordMul_ι X (l + m) k]
  simp only [Category.assoc]

omit [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Right-associated component of associativity: associator naturality plus
two multiplications reduce to the right-nested `tensorPowObj_add` inverses. -/
private theorem tensorWordMulAssoc_right (X : C) (l m k : ℕ) :
    ((tensorWordι X l ⊗ₘ tensorWordι X m) ⊗ₘ tensorWordι X k) ≫
      ((α_ (tensorWordObj X) (tensorWordObj X) (tensorWordObj X)).hom ≫
        ((tensorWordObj X ◁ tensorWordMul X) ≫ tensorWordMul X)) =
      (((α_ (tensorPowObj X l) (tensorPowObj X m) (tensorPowObj X k)).hom ≫
        ((𝟙 (tensorPowObj X l) ⊗ₘ (tensorPowObj_add X m k).inv) ≫
          (tensorPowObj_add X l (m+k)).inv)) ≫
        tensorWordι X (l+(m+k))) := by
  rw [MonoidalCategory.associator_naturality_assoc,
    MonoidalCategory.tensorHom_def'_assoc,
    ← MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    tensorWordMul_ι X m k,
    MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.tensorHom_def'_assoc,
    tensorWordMul_ι X l (m + k)]
  simp only [← MonoidalCategory.id_tensorHom, Category.assoc]

omit [∀ (f : ℕ → C), HasCoproduct f]
  [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Coherence key: the two reassociated `tensorPowObj_add` routes agree by
`tensorPowObj_add_assoc` plus standard reassociated coherence. -/
private theorem tensorWordMulAssoc_key (X : C) (l m k : ℕ) :
    ((((tensorPowObj_add X l m).inv ⊗ₘ 𝟙 (tensorPowObj X k)) ≫
      (tensorPowObj_add X (l+m) k).inv) ≫
      eqToHom (congrArg (tensorPowObj X) (Nat.add_assoc l m k))) =
      ((α_ (tensorPowObj X l) (tensorPowObj X m) (tensorPowObj X k)).hom ≫
        ((𝟙 (tensorPowObj X l) ⊗ₘ (tensorPowObj_add X m k).inv) ≫
          (tensorPowObj_add X l (m+k)).inv)) := by
    let L : ((tensorPowObj X l ⊗ tensorPowObj X m) ⊗ tensorPowObj X k) ≅
        tensorPowObj X (l + (m + k)) :=
      ((tensorIso (tensorPowObj_add X l m)
        (Iso.refl (tensorPowObj X k))).symm ≪≫
      (tensorPowObj_add X (l + m) k).symm) ≪≫
      eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc l m k))
    let R : ((tensorPowObj X l ⊗ tensorPowObj X m) ⊗ tensorPowObj X k) ≅
        tensorPowObj X (l + (m + k)) :=
      (α_ (tensorPowObj X l) (tensorPowObj X m) (tensorPowObj X k)) ≪≫
      (tensorIso (Iso.refl (tensorPowObj X l))
        (tensorPowObj_add X m k).symm) ≪≫
      (tensorPowObj_add X l (m + k)).symm
    change L.hom = R.hom
    rw [← Iso.inv_eq_inv]
    simp only [L, R, Iso.trans_inv, Iso.symm_inv]
    simp only [Category.assoc]
    rw [Iso.inv_comp_eq (eqToIso (congrArg (tensorPowObj X)
      (Nat.add_assoc l m k)))]
    simp only [← Category.assoc]
    rw [Iso.eq_comp_inv (α_ (tensorPowObj X l) (tensorPowObj X m)
      (tensorPowObj X k))]
    simp only [Category.assoc]
    exact (tensorPowObj_add_assoc X l m k).symm

/-- Associativity via `tensorPowObj_add_assoc`. -/
theorem tensorWordMulAssoc (X : C) :
    tensorWordMul X ▷ tensorWordObj X ≫ tensorWordMul X =
      (α_ (tensorWordObj X) (tensorWordObj X) (tensorWordObj X)).hom ≫
        tensorWordObj X ◁ tensorWordMul X ≫ tensorWordMul X := by
  apply tensorWord_hom_ext_triple
  intro l m k
  have hL := tensorWordMulAssoc_left X l m k
  have hR := tensorWordMulAssoc_right X l m k
  have hIdx : tensorWordι X ((l+m)+k) =
      eqToHom (congrArg (tensorPowObj X) (Nat.add_assoc l m k)) ≫
        tensorWordι X (l+(m+k)) := by
    unfold tensorWordι
    have h := Limits.Sigma.eqToHom_comp_ι (fun n : ℕ => tensorPowObj X n)
      (Nat.add_assoc l m k)
    exact ((CategoryTheory.eqToHom_comp_iff _ _ _).mpr h.symm).symm
  have key := tensorWordMulAssoc_key X l m k
  rw [hL, hR, hIdx]
  have aF : (((((tensorPowObj_add X l m).inv ⊗ₘ 𝟙 (tensorPowObj X k)) ≫
      (tensorPowObj_add X (l+m) k).inv) ≫
      (eqToHom (congrArg (tensorPowObj X) (Nat.add_assoc l m k)) ≫
        tensorWordι X (l+(m+k))))) =
      ((((((tensorPowObj_add X l m).inv ⊗ₘ 𝟙 (tensorPowObj X k)) ≫
        (tensorPowObj_add X (l+m) k).inv) ≫
        eqToHom (congrArg (tensorPowObj X) (Nat.add_assoc l m k))) ≫
        tensorWordι X (l+(m+k)))) :=
    (Category.assoc _ _ _).symm
  rw [aF]
  exact congrArg (· ≫ tensorWordι X (l + (m + k))) key

/-- `MonObj` instance with explicit unit/multiplication laws. -/
noncomputable instance tensorWordMonObj (X : C) : MonObj (tensorWordObj X) where
  one := tensorWordOne X
  mul := tensorWordMul X
  one_mul := tensorWordOneMul X
  mul_one := tensorWordMulOne X
  mul_assoc := tensorWordMulAssoc X

/-- Bundled monoid object. -/
noncomputable def tensorWordMon (X : C) : Mon C :=
  Mon.mk (tensorWordObj X)

/-- Functorial action on maps preserves unit and multiplication. -/
noncomputable instance tensorWordIsMonHom {X Y : C} (f : X ⟶ Y) :
    IsMonHom (tensorWordMap f) where
  one_hom := by
    change tensorWordι X 0 ≫ tensorWordMap f = tensorWordι Y 0
    rw [tensorWordMap_ι]
    exact Category.id_comp _
  mul_hom := by
    change tensorWordMul X ≫ tensorWordMap f =
      (tensorWordMap f ⊗ₘ tensorWordMap f) ≫ tensorWordMul Y
    apply tensorWord_hom_ext
    intro n m
    have hR : ((tensorWordι X n ⊗ₘ tensorWordι X m) ≫
        (tensorWordMap f ⊗ₘ tensorWordMap f)) ≫ tensorWordMul Y =
        (((tensorPowMap f n ⊗ₘ tensorPowMap f m) ≫
          (tensorPowObj_add Y n m).inv) ≫ tensorWordι Y (n + m)) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp only [tensorWordMap_ι]
      rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc,
        tensorWordMul_ι, ← Category.assoc]
    simp only [← Category.assoc]
    rw [tensorWordMul_ι, hR]
    simp only [Category.assoc, tensorWordMap_ι]
    have hNat := tensorPowObj_add_naturality f n m
    have hInv : (tensorPowMap f n ⊗ₘ tensorPowMap f m) ≫
        (tensorPowObj_add Y n m).inv =
        (tensorPowObj_add X n m).inv ≫ tensorPowMap f (n + m) := by
      apply (cancel_epi (tensorPowObj_add X n m).hom).mp
      simp only [← Category.assoc]
      rw [← hNat]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Category.id_comp]
    simp only [← Category.assoc, hInv]

/-- Bundled functor `C ⥤ Mon C`. -/
noncomputable def tensorWordFunctor : C ⥤ Mon C where
  obj X := tensorWordMon X
  map f := Mon.ofHom (tensorWordMap f)
  map_id X := by
    apply Mon.Hom.ext'
    change tensorWordMap (𝟙 X) = 𝟙 (tensorWordObj X)
    exact tensorWordMap_id X
  map_comp f g := by
    apply Mon.Hom.ext'
    change tensorWordMap (f ≫ g) = tensorWordMap f ≫ tensorWordMap g
    exact (tensorWordMap_comp f g).symm

/-- Carrier projection of the tensor-word functor. -/
@[simp]
theorem tensorWordFunctor_obj_carrier (X : C) :
    ((tensorWordFunctor (C := C)).obj X).X = tensorWordObj X :=
  rfl

/-- Morphism projection of the tensor-word functor. -/
@[simp]
theorem tensorWordFunctor_map_hom {X Y : C} (f : X ⟶ Y) :
    ((tensorWordFunctor (C := C)).map f).hom = tensorWordMap f :=
  rfl

omit [∀ (f : ℕ → C), HasCoproduct f]
  [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Recursive evaluation of tensor powers into a monoid object.
Private recursive assembly used only by the public lift; not for downstream use. -/
private noncomputable def tensorPowEval {X : C} (M : Mon C) (f : X ⟶ M.X)
    (n : ℕ) : tensorPowObj X n ⟶ M.X :=
  Nat.rec (motive := fun n => tensorPowObj X n ⟶ M.X)
    MonObj.one (fun _ ih => (ih ⊗ₘ f) ≫ MonObj.mul) n

omit [∀ (f : ℕ → C), HasCoproduct f]
  [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
private theorem tensorPowEval_zero {X : C} (M : Mon C) (f : X ⟶ M.X) :
    tensorPowEval M f 0 = MonObj.one :=
  rfl

omit [∀ (f : ℕ → C), HasCoproduct f]
  [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
private theorem tensorPowEval_succ {X : C} (M : Mon C) (f : X ⟶ M.X) (n : ℕ) :
    tensorPowEval M f (n + 1) =
      ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul) :=
  rfl

omit [∀ (f : ℕ → C), HasCoproduct f]
  [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Evaluation respects the add coherence iso. -/
private theorem tensorPowEval_add {X : C} (M : Mon C) (f : X ⟶ M.X) (m n : ℕ) :
    tensorPowEval M f (m + n) =
      (tensorPowObj_add X m n).hom ≫
        ((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul) := by
  induction n generalizing m with
  | zero =>
    have hMul := MonObj.mul_one_hom (tensorPowEval M f m)
    have hAdd := tensorPowObj_add_zero_right X m
    have E0 : ((tensorPowEval M f m ⊗ₘ tensorPowEval M f 0) ≫ MonObj.mul)
        = ((tensorPowEval M f m ⊗ₘ MonObj.one) ≫ MonObj.mul) :=
      congrArg (fun x => (tensorPowEval M f m ⊗ₘ x) ≫ MonObj.mul)
        (tensorPowEval_zero M f)
    have hRHS : (tensorPowObj_add X m 0).hom ≫
          ((tensorPowEval M f m ⊗ₘ tensorPowEval M f 0) ≫ MonObj.mul)
        = tensorPowEval M f m := by
      rw [hAdd, E0, hMul]
      change (ρ_ (tensorPowObj X m)).symm.hom ≫
        ((ρ_ (tensorPowObj X m)).hom ≫ tensorPowEval M f m) = _
      exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (Iso.inv_hom_id _)).trans (Category.id_comp _)))
    exact hRHS.symm
  | succ n ih =>
    have hIso : (tensorIso (tensorPowObj_add X m n) (Iso.refl X)).hom =
        (tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X := rfl
    have hEvalSucc : tensorPowEval M f (n + 1) =
        ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul) := rfl
    have hAdd' : (tensorPowObj_add X m (n + 1)).hom =
        (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
          (associator (tensorPowObj X m) (tensorPowObj X n) X).hom) := by
      have hDef : (tensorPowObj_add X m (n + 1)).hom =
          (tensorIso (tensorPowObj_add X m n) (Iso.refl X)).hom ≫
            (associator (tensorPowObj X m) (tensorPowObj X n) X).hom := rfl
      rw [hDef, hIso]
    have STEP2 : ((((tensorPowObj_add X m n).hom ≫
              ((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul))) ⊗ₘ f)
          = ((((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X)) ≫
            ((((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul)) ⊗ₘ f)) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
    have STEP_B : (((((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul)) ⊗ₘ f) ≫
            MonObj.mul)
          = (associator (tensorPowObj X m) (tensorPowObj X n) X).hom ≫
              ((((tensorPowEval M f m ⊗ₘ
                ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul))) ≫ MonObj.mul)) := by
      simp only [mon_tauto]
    change tensorPowEval M f ((m + n) + 1) =
      (tensorPowObj_add X m (n + 1)).hom ≫
        ((tensorPowEval M f m ⊗ₘ tensorPowEval M f (n + 1)) ≫ MonObj.mul)
    have E_ih : ((tensorPowEval M f (m + n) ⊗ₘ f) ≫ MonObj.mul) =
        ((((tensorPowObj_add X m n).hom ≫
              ((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul))) ⊗ₘ f) ≫
            MonObj.mul :=
      congrArg (fun y => (y ≫ MonObj.mul))
        (congrArg (fun x => (x ⊗ₘ f)) (ih m))
    have F1 : tensorPowEval M f ((m + n) + 1) =
        ((((tensorPowObj_add X m n).hom ≫
              ((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul))) ⊗ₘ f) ≫
            MonObj.mul :=
      (tensorPowEval_succ M f (m + n)).trans E_ih
    have F2 : ((((tensorPowObj_add X m n).hom ≫
              ((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul))) ⊗ₘ f) ≫
            MonObj.mul =
        ((((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
              ((((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul)) ⊗ₘ f))) ≫
            MonObj.mul :=
      congrArg (fun z => z ≫ MonObj.mul) STEP2
    have F3 : ((((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
              ((((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul)) ⊗ₘ f))) ≫
            MonObj.mul =
        ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
              (((((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul)) ⊗ₘ f) ≫
                MonObj.mul) :=
      Category.assoc _ _ _
    have F4 : ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
              (((((tensorPowEval M f m ⊗ₘ tensorPowEval M f n) ≫ MonObj.mul)) ⊗ₘ f) ≫
                MonObj.mul) =
        ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
              ((associator (tensorPowObj X m) (tensorPowObj X n) X).hom ≫
                ((((tensorPowEval M f m ⊗ₘ
                  ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul))) ≫ MonObj.mul))) :=
      congrArg
        (fun w => ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫ w)
        STEP_B
    have F5 : ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
              ((associator (tensorPowObj X m) (tensorPowObj X n) X).hom ≫
                ((((tensorPowEval M f m ⊗ₘ
                  ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul))) ≫ MonObj.mul))) =
        ((((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
              (associator (tensorPowObj X m) (tensorPowObj X n) X).hom) ≫
              (((tensorPowEval M f m ⊗ₘ
                ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul)) ≫ MonObj.mul))) :=
      (Category.assoc _ _ _).symm
    have F6 : ((((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
              (associator (tensorPowObj X m) (tensorPowObj X n) X).hom) ≫
              (((tensorPowEval M f m ⊗ₘ
                ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul)) ≫ MonObj.mul))) =
        (tensorPowObj_add X m (n + 1)).hom ≫
              ((((tensorPowEval M f m ⊗ₘ
                ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul))) ≫ MonObj.mul)) :=
      congrArg
        (fun q => q ≫ ((((tensorPowEval M f m ⊗ₘ
              ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul))) ≫ MonObj.mul)))
        hAdd'.symm
    have F7 : (tensorPowObj_add X m (n + 1)).hom ≫
              ((((tensorPowEval M f m ⊗ₘ
                ((tensorPowEval M f n ⊗ₘ f) ≫ MonObj.mul))) ≫ MonObj.mul)) =
        (tensorPowObj_add X m (n + 1)).hom ≫
              ((tensorPowEval M f m ⊗ₘ tensorPowEval M f (n + 1)) ≫ MonObj.mul) :=
      congrArg ((tensorPowObj_add X m (n + 1)).hom ≫ ·)
        (congrArg (fun z => z ≫ MonObj.mul)
          (congrArg (tensorPowEval M f m ⊗ₘ ·) hEvalSucc.symm))
    exact F1.trans (F2.trans (F3.trans (F4.trans (F5.trans (F6.trans F7)))))

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Degree-one generator via the left unitor. -/
noncomputable def tensorWordGenerator (X : C) : X ⟶ tensorWordObj X :=
  (λ_ X).inv ≫ tensorWordι X (0 + 1)

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Naturality of the degree-one generator under functorial maps. -/
theorem tensorWordGenerator_naturality {Y X : C} (h : Y ⟶ X) :
    tensorWordGenerator Y ≫ tensorWordMap h =
      h ≫ tensorWordGenerator X := by
  change ((λ_ Y).inv ≫ tensorWordι Y (0 + 1)) ≫ tensorWordMap h =
    h ≫ ((λ_ X).inv ≫ tensorWordι X (0 + 1))
  have hPow : tensorPowMap h (0 + 1) = (𝟙 (𝟙_ C) ⊗ₘ h) := rfl
  have hMapι : tensorWordι Y (0 + 1) ≫ tensorWordMap h =
      tensorPowMap h (0 + 1) ≫ tensorWordι X (0 + 1) :=
    tensorWordMap_ι h (0 + 1)
  have hInv : (λ_ Y).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ h) = h ≫ (λ_ X).inv := by
    simpa only [MonoidalCategory.id_tensorHom] using
      (MonoidalCategory.leftUnitor_inv_naturality h).symm
  calc ((λ_ Y).inv ≫ tensorWordι Y (0 + 1)) ≫ tensorWordMap h
      = (λ_ Y).inv ≫ (tensorWordι Y (0 + 1) ≫ tensorWordMap h) :=
        Category.assoc _ _ _
    _ = (λ_ Y).inv ≫ (tensorPowMap h (0 + 1) ≫ tensorWordι X (0 + 1)) :=
        congrArg _ hMapι
    _ = (λ_ Y).inv ≫ ((𝟙 (𝟙_ C) ⊗ₘ h) ≫ tensorWordι X (0 + 1)) :=
        congrArg (fun x => (λ_ Y).inv ≫ (x ≫ tensorWordι X (0 + 1))) hPow
    _ = ((λ_ Y).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ h)) ≫ tensorWordι X (0 + 1) :=
        (Category.assoc _ _ _).symm
    _ = (h ≫ (λ_ X).inv) ≫ tensorWordι X (0 + 1) :=
        congrArg (· ≫ _) hInv
    _ = h ≫ ((λ_ X).inv ≫ tensorWordι X (0 + 1)) :=
        Category.assoc _ _ _

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Coproduct-descended lift of a generator map. The family is inlined so the
public API does not reference the private recursive evaluator by name. -/
noncomputable def tensorWordLift {X : C} (M : Mon C) (f : X ⟶ M.X) :
    tensorWordObj X ⟶ M.X :=
  Limits.Sigma.desc fun n : ℕ =>
    Nat.rec (motive := fun n => tensorPowObj X n ⟶ M.X)
      MonObj.one (fun _ ih => (ih ⊗ₘ f) ≫ MonObj.mul) n

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- Computation of the public lift through the recursive evaluator. -/
private theorem tensorWordLift_eval {X : C} (M : Mon C) (f : X ⟶ M.X) (k : ℕ) :
    tensorWordι X k ≫ tensorWordLift M f = tensorPowEval M f k :=
  Limits.Sigma.ι_comp_desc _ _

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- The single generator beta law. -/
theorem tensorWordLift_beta {X : C} (M : Mon C) (f : X ⟶ M.X) :
    tensorWordGenerator X ≫ tensorWordLift M f = f := by
  change ((λ_ X).inv ≫ tensorWordι X (0 + 1)) ≫ tensorWordLift M f = f
  have hι : tensorWordι X (0 + 1) ≫ tensorWordLift M f =
      tensorPowEval M f (0 + 1) :=
    tensorWordLift_eval M f _
  have hE01 : tensorPowEval M f (0 + 1) =
      ((MonObj.one ⊗ₘ f) ≫ MonObj.mul) :=
    (tensorPowEval_succ M f 0).trans
      (congrArg (· ≫ MonObj.mul)
        (congrArg (· ⊗ₘ f) (tensorPowEval_zero M f)))
  calc ((λ_ X).inv ≫ tensorWordι X (0 + 1)) ≫ tensorWordLift M f
      = (λ_ X).inv ≫ (tensorWordι X (0 + 1) ≫ tensorWordLift M f) :=
        Category.assoc _ _ _
    _ = (λ_ X).inv ≫ ((MonObj.one ⊗ₘ f) ≫ MonObj.mul) :=
        congrArg _ (hι.trans hE01)
    _ = f := Mathlib.Tactic.MonTauto.leftUnitor_inv_one_tensor_mul f

/-- The lift preserves unit and multiplication. -/
noncomputable instance tensorWordLiftIsMonHom {X : C} (M : Mon C)
    (f : X ⟶ M.X) : IsMonHom (tensorWordLift M f) where
  one_hom := by
    change tensorWordOne X ≫ tensorWordLift M f = MonObj.one
    have hDesc : tensorWordι X 0 ≫ tensorWordLift M f =
        tensorPowEval M f 0 :=
      tensorWordLift_eval M f 0
    exact hDesc.trans (tensorPowEval_zero M f)
  mul_hom := by
    apply tensorWord_hom_ext
    intro n m
    have hMul := tensorWordMul_ι X n m
    have hEval := tensorPowEval_add M f n m
    have hDesc : tensorWordι X (n + m) ≫ tensorWordLift M f =
        tensorPowEval M f (n + m) :=
      tensorWordLift_eval M f _
    have hDescN : tensorWordι X n ≫ tensorWordLift M f =
        tensorPowEval M f n :=
      tensorWordLift_eval M f _
    have hDescM : tensorWordι X m ≫ tensorWordLift M f =
        tensorPowEval M f m :=
      tensorWordLift_eval M f _
    calc (tensorWordι X n ⊗ₘ tensorWordι X m) ≫
            tensorWordMul X ≫ tensorWordLift M f
        = ((tensorPowObj_add X n m).inv ≫ tensorWordι X (n + m)) ≫
            tensorWordLift M f := by
          rw [← Category.assoc, hMul]
        _ = (tensorPowObj_add X n m).inv ≫ tensorPowEval M f (n + m) := by
          rw [Category.assoc, hDesc]
        _ = (tensorPowEval M f n ⊗ₘ tensorPowEval M f m) ≫ MonObj.mul := by
          rw [hEval, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        _ = ((tensorWordι X n ≫ tensorWordLift M f) ⊗ₘ
            (tensorWordι X m ≫ tensorWordLift M f)) ≫ MonObj.mul := by
          rw [hDescN, hDescM]
        _ = ((tensorWordι X n ⊗ₘ tensorWordι X m) ≫
            (tensorWordLift M f ⊗ₘ tensorWordLift M f)) ≫ MonObj.mul := by
          rw [MonoidalCategory.tensorHom_comp_tensorHom]
        _ = (tensorWordι X n ⊗ₘ tensorWordι X m) ≫
            ((tensorWordLift M f ⊗ₘ tensorWordLift M f) ≫ MonObj.mul) := by
          rw [Category.assoc]

/-- Bundled monoid morphism from the lift. -/
noncomputable def tensorWordLiftHom {X : C} (M : Mon C) (f : X ⟶ M.X) :
    tensorWordMon X ⟶ M :=
  Mon.ofHom (tensorWordLift M f)

/-- Uniqueness of the monoid extension via coproduct induction. -/
theorem tensorWordLiftUnique {X : C} {M : Mon C} (f : X ⟶ M.X)
    (g : tensorWordMon X ⟶ M)
    (h : tensorWordGenerator X ≫ g.hom = f) :
    g = tensorWordLiftHom M f := by
  apply Mon.Hom.ext'
  change g.hom = tensorWordLift M f
  -- The underlying carrier map, stated at `tensorWordObj` so that all
  -- compositions below are syntactically well-typed.
  let gword : tensorWordObj X ⟶ M.X := g.hom
  have hg : tensorWordGenerator X ≫ gword = f := h
  have hMulG : tensorWordMul X ≫ gword =
      (gword ⊗ₘ gword) ≫ MonObj.mul :=
    IsMonHom.mul_hom g.hom
  have hLift : ∀ k : ℕ, tensorWordι X k ≫ tensorWordLift M f =
      tensorPowEval M f k := fun k => tensorWordLift_eval M f k
  have key : ∀ n : ℕ, tensorWordι X n ≫ gword = tensorPowEval M f n := by
    intro n
    induction n with
    | zero =>
      exact IsMonHom.one_hom g.hom
    | succ n ih =>
      have hG : tensorWordGenerator X =
          ((λ_ X).inv ≫ tensorWordι X 1) := rfl
      have hL : (λ_ X).inv ≫ (tensorWordι X 1 ≫ gword) = f :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ gword) hG).symm.trans hg)
      have hI : tensorWordι X 1 ≫ gword = (λ_ X).hom ≫ f := by
        have h2 : (λ_ X).hom ≫
              ((λ_ X).inv ≫ (tensorWordι X 1 ≫ gword))
            = tensorWordι X 1 ≫ gword :=
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (Iso.hom_inv_id _))).trans
            (Category.id_comp _)
        exact h2.symm.trans (congrArg _ hL)
      have hE : tensorPowEval M f 1 = (λ_ X).hom ≫ f :=
        MonObj.one_mul_hom f
      have hAddU := tensorPowEval_add M f n 1
      have STEP_ii : ((tensorWordι X n ≫ gword) ⊗ₘ
            (tensorWordι X 1 ≫ gword))
          = ((tensorPowEval M f n) ⊗ₘ ((λ_ X).hom ≫ f)) :=
        (congrArg (· ⊗ₘ (tensorWordι X 1 ≫ gword)) ih).trans
          (congrArg (tensorPowEval M f n ⊗ₘ ·) hI)
      calc tensorWordι X (n + 1) ≫ gword
          = (((tensorPowObj_add X n 1).hom ≫
                (tensorPowObj_add X n 1).inv) ≫
              (tensorWordι X (n + 1) ≫ gword)) :=
            ((Category.id_comp _).symm.trans
              (congrArg (· ≫ _) (Iso.hom_inv_id _).symm))
        _ = (tensorPowObj_add X n 1).hom ≫
              ((tensorPowObj_add X n 1).inv ≫
                (tensorWordι X (n + 1) ≫ gword)) :=
            Category.assoc _ _ _
        _ = (tensorPowObj_add X n 1).hom ≫
              ((((tensorWordι X n ⊗ₘ tensorWordι X 1) ≫ tensorWordMul X)) ≫
                gword) :=
            congrArg ((tensorPowObj_add X n 1).hom ≫ ·)
              ((Category.assoc _ _ _).symm.trans
                (congrArg (· ≫ gword) (tensorWordMul_ι X n 1).symm))
        _ = (tensorPowObj_add X n 1).hom ≫
              ((tensorWordι X n ⊗ₘ tensorWordι X 1) ≫
                (tensorWordMul X ≫ gword)) :=
            congrArg _ (Category.assoc _ _ _)
        _ = (tensorPowObj_add X n 1).hom ≫
              ((tensorWordι X n ⊗ₘ tensorWordι X 1) ≫
                ((gword ⊗ₘ gword) ≫ MonObj.mul)) :=
            congrArg _ (congrArg _ hMulG)
        _ = (tensorPowObj_add X n 1).hom ≫
              ((((tensorWordι X n ≫ gword) ⊗ₘ
                (tensorWordι X 1 ≫ gword))) ≫ MonObj.mul) :=
            congrArg ((tensorPowObj_add X n 1).hom ≫ ·)
              ((Category.assoc _ _ _).symm.trans
                (congrArg (· ≫ MonObj.mul)
                  (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _)))
        _ = (tensorPowObj_add X n 1).hom ≫
              ((((tensorPowEval M f n) ⊗ₘ ((λ_ X).hom ≫ f))) ≫ MonObj.mul) :=
            congrArg ((tensorPowObj_add X n 1).hom ≫ ·)
              (congrArg (· ≫ MonObj.mul) STEP_ii)
        _ = tensorPowEval M f (n + 1) :=
            (congrArg
              (fun x => (tensorPowObj_add X n 1).hom ≫
                ((tensorPowEval M f n ⊗ₘ x) ≫ MonObj.mul)) hE.symm).trans
              hAddU.symm
  apply Limits.Sigma.hom_ext
  intro n
  change tensorWordι X n ≫ gword = tensorWordι X n ≫ tensorWordLift M f
  exact (key n).trans (hLift n).symm

/-- Generator-map/monoid-hom equivalence. -/
noncomputable def tensorWordHomEquiv (X : C) (M : Mon C) :
    (X ⟶ M.X) ≃ (tensorWordMon X ⟶ M) where
  toFun f := tensorWordLiftHom M f
  invFun g := tensorWordGenerator X ≫ g.hom
  left_inv f := tensorWordLift_beta M f
  right_inv g := (tensorWordLiftUnique _ g rfl).symm

/-- Target naturality of the equivalence. -/
theorem tensorWordHomEquiv_target {X : C} {M N : Mon C} (f : X ⟶ M.X)
    (k : M ⟶ N) :
    tensorWordHomEquiv X N (f ≫ k.hom) =
      ((tensorWordHomEquiv X M) f ≫ k) := by
  apply Eq.symm
  apply tensorWordLiftUnique
  change tensorWordGenerator X ≫
    (((tensorWordLiftHom M f) ≫ k).hom) = f ≫ k.hom
  have hB := tensorWordLift_beta M f
  calc tensorWordGenerator X ≫
          (((tensorWordLiftHom M f) ≫ k).hom)
      = tensorWordGenerator X ≫
          (tensorWordLift M f ≫ k.hom) := rfl
    _ = (tensorWordGenerator X ≫ tensorWordLift M f) ≫ k.hom := by
        rw [Category.assoc]
    _ = f ≫ k.hom := by
        rw [hB]

/-- Evaluation of a monoid morphism out of the tensor word: at every
length it agrees with the lift of its generator value. -/
theorem tensorWordι_comp_monHom {X : C} {M : Mon C} (g : tensorWordMon X ⟶ M)
    (n : ℕ) :
    tensorWordι X n ≫ g.hom =
      tensorWordι X n ≫ tensorWordLift M (tensorWordGenerator X ≫ g.hom) := by
  have hg : tensorWordLiftHom M (tensorWordGenerator X ≫ g.hom) = g :=
    (tensorWordHomEquiv X M).right_inv g
  exact congrArg (fun k : tensorWordMon X ⟶ M => tensorWordι X n ≫ k.hom)
    hg.symm

/-- Length-one evaluation of a monoid morphism out of the tensor word:
the unitor-prefaced generator value. -/
theorem tensorWordι_one_comp_monHom {X : C} {M : Mon C}
    (g : tensorWordMon X ⟶ M) :
    tensorWordι X 1 ≫ g.hom =
      (λ_ X).hom ≫ (tensorWordGenerator X ≫ g.hom) := by
  have hgen : tensorWordGenerator X = (λ_ X).inv ≫ tensorWordι X 1 := rfl
  have hι : tensorWordι X 1 = (λ_ X).hom ≫ tensorWordGenerator X := by
    rw [hgen]
    exact (CategoryTheory.Iso.hom_inv_id_assoc (λ_ X) (tensorWordι X 1)).symm
  have step1 : tensorWordι X 1 ≫ g.hom =
      tensorWordι X 1 ≫
        tensorWordLift M (tensorWordGenerator X ≫ g.hom) :=
    tensorWordι_comp_monHom g 1
  have step2 : tensorWordι X 1 ≫
        tensorWordLift M (tensorWordGenerator X ≫ g.hom) =
      (λ_ X).hom ≫ (tensorWordGenerator X ≫ g.hom) :=
    ((congrArg (· ≫ tensorWordLift M (tensorWordGenerator X ≫ g.hom))
      hι).trans (Category.assoc _ _ _)).trans
      (congrArg ((λ_ X).hom ≫ ·) (tensorWordLift_beta M _))
  exact step1.trans step2

/-- Length-two evaluation of a monoid morphism out of the tensor word:
the recursive evaluation, one multiplication of the length-one value
with the generator value. -/
theorem tensorWordι_two_comp_monHom {X : C} {M : Mon C}
    (g : tensorWordMon X ⟶ M) :
    tensorWordι X 2 ≫ g.hom =
      (((MonObj.one ⊗ₘ (tensorWordGenerator X ≫ g.hom)) ≫ MonObj.mul) ⊗ₘ
        (tensorWordGenerator X ≫ g.hom)) ≫ MonObj.mul := by
  have e1 : tensorPowEval M (tensorWordGenerator X ≫ g.hom) 1 =
      (MonObj.one ⊗ₘ (tensorWordGenerator X ≫ g.hom)) ≫ MonObj.mul := rfl
  have e2 : tensorPowEval M (tensorWordGenerator X ≫ g.hom) 2 =
      ((tensorPowEval M (tensorWordGenerator X ≫ g.hom) 1 ⊗ₘ
        (tensorWordGenerator X ≫ g.hom)) ≫ MonObj.mul) := rfl
  have step1 : tensorWordι X 2 ≫ g.hom =
      tensorWordι X 2 ≫
        tensorWordLift M (tensorWordGenerator X ≫ g.hom) :=
    tensorWordι_comp_monHom g 2
  have step2 : tensorWordι X 2 ≫
        tensorWordLift M (tensorWordGenerator X ≫ g.hom) =
      tensorPowEval M (tensorWordGenerator X ≫ g.hom) 2 :=
    tensorWordLift_eval M _ _
  have step3 : tensorPowEval M (tensorWordGenerator X ≫ g.hom) 2 =
      (((MonObj.one ⊗ₘ (tensorWordGenerator X ≫ g.hom)) ≫ MonObj.mul) ⊗ₘ
        (tensorWordGenerator X ≫ g.hom)) ≫ MonObj.mul :=
    e2.trans (congrArg
      (fun y => (y ⊗ₘ (tensorWordGenerator X ≫ g.hom)) ≫ MonObj.mul) e1)
  exact step1.trans (step2.trans step3)

/-- Source naturality of the equivalence. -/
theorem tensorWordHomEquiv_source {Y X : C} {M : Mon C} (h : Y ⟶ X)
    (f : X ⟶ M.X) :
    tensorWordHomEquiv Y M (h ≫ f) =
      ((Mon.ofHom (tensorWordMap h)) ≫ (tensorWordHomEquiv X M) f) := by
  apply Eq.symm
  apply tensorWordLiftUnique
  have hB := tensorWordLift_beta (M := M) (f := f)
  have hGen : tensorWordGenerator Y ≫ tensorWordMap h =
      h ≫ tensorWordGenerator X :=
    tensorWordGenerator_naturality h
  change tensorWordGenerator Y ≫
    (((Mon.ofHom (tensorWordMap h) ≫ tensorWordLiftHom M f).hom)) =
      h ≫ f
  calc tensorWordGenerator Y ≫
          ((Mon.ofHom (tensorWordMap h) ≫ tensorWordLiftHom M f).hom)
      = tensorWordGenerator Y ≫
          (tensorWordMap h ≫ tensorWordLift M f) := rfl
    _ = (tensorWordGenerator Y ≫ tensorWordMap h) ≫
          tensorWordLift M f := by
        rw [Category.assoc]
    _ = (h ≫ tensorWordGenerator X) ≫ tensorWordLift M f := by
        rw [hGen]
    _ = h ≫ (tensorWordGenerator X ≫ tensorWordLift M f) := by
        rw [Category.assoc]
    _ = h ≫ f := by
        rw [hB]

end CategoryTheory.MonoidalCategory.TensorWord

end
