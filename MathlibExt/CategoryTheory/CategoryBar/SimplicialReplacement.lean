/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.Change

/-!
# Simplicial replacement: terminal right coefficient

For `C : Type u` with `Category.{v} C` and `L : C ⥤ Type uL`, the simplicial
replacement is the transparent specialization of the two-sided category bar
with the terminal right coefficient `replUnit C : Cᵒᵖ ⥤ Type 0`. The degree-`n`
object is `Σ F : ComposableArrows C n, (L.obj F.left × (replUnit C).obj (op F.right))`.

Chain orientation: `L` is at `F.left` (source), while `replUnit` is the right
coefficient at `op F.right` (target). The right coefficient is plain `PUnit`.
Faces are inherited from the bar, so `d₀` acts through `L` and the last face
through the terminal right coefficient.

Provenance: transparent specialization of the `Basic` two-sided category bar
at the terminal right coefficient; same nLab/Shulman two-sided bar sources as
`Basic` (`arXiv:math/0610194`), strict ordinary specialization only.

Nonclaims: no category-of-elements or nerve comparison,
and no comma/Grothendieck results.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v uL

namespace CategoryTheory

namespace CategoryBar

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {L L' : C ⥤ Type uL}

/-- Terminal right coefficient: the constant `PUnit`-valued presheaf. -/
def replUnit (C : Type u) [Category.{v} C] : Cᵒᵖ ⥤ Type 0 :=
  (Functor.const Cᵒᵖ).obj PUnit

/-- Identity coefficient map into the pushed-forward terminal coefficient. -/
def replUnitMap (Φ : C ⥤ D) : replUnit C ⟶ Φ.op ⋙ replUnit D where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- Degree-`n` simplicial replacement object. -/
abbrev replObj (C : Type u) [Category.{v} C] (L : C ⥤ Type uL)
    (n : ℕ) : Type (max u v uL) :=
  barObj C (replUnit C) L n

/-- Simplicial replacement data: the category bar at the terminal coefficient. -/
noncomputable def simplicialReplacementData (L : C ⥤ Type uL) :
    SimplicialObject.Data (Type (max u v uL)) :=
  categoryBarData (R := replUnit C) (L := L)

/-- Simplicial replacement as a simplicial set. -/
noncomputable def simplicialReplacement (L : C ⥤ Type uL) : SSet.{max u v uL} :=
  categoryBar (R := replUnit C) (L := L)

@[simp]
theorem simplicialReplacementData_obj (n : ℕ) :
    (simplicialReplacementData L).obj n = replObj C L n :=
  rfl

@[simp]
theorem simplicialReplacementData_δ {n : ℕ} (i : Fin (n + 2)) :
    (simplicialReplacementData L).δ i =
      ↾(barδ (R := replUnit C) (L := L) i) :=
  rfl

@[simp]
theorem simplicialReplacementData_σ {n : ℕ} (i : Fin (n + 1)) :
    (simplicialReplacementData L).σ i =
      ↾(barσ (R := replUnit C) (L := L) i) :=
  rfl

@[simp]
theorem simplicialReplacement_obj (n : ℕ) :
    (simplicialReplacement L).obj (op (SimplexCategory.mk n)) = replObj C L n :=
  rfl

@[simp]
theorem simplicialReplacement_map_δ {n : ℕ} (i : Fin (n + 2)) :
    (simplicialReplacement L).map (SimplexCategory.δ i).op =
      ↾(barδ (R := replUnit C) (L := L) i) := by
  simp [simplicialReplacement]

@[simp]
theorem simplicialReplacement_map_σ {n : ℕ} (i : Fin (n + 1)) :
    (simplicialReplacement L).map (SimplexCategory.σ i).op =
      ↾(barσ (R := replUnit C) (L := L) i) := by
  simp [simplicialReplacement]

/-- Degree-zero description: a `0`-simplex is an object with an `L`-coefficient,
the terminal `PUnit` factor eliminated. -/
noncomputable def replObjZeroEquiv (L : C ⥤ Type uL) :
    replObj C L 0 ≃ Σ X : C, L.obj X where
  toFun
    | ⟨F, l, _⟩ => ⟨F.obj 0, l⟩
  invFun
    | ⟨X, l⟩ => ⟨ComposableArrows.mk₀ X, l, PUnit.unit⟩
  left_inv := by
    rintro ⟨F, l, r⟩
    have hChain : ComposableArrows.mk₀ (F.obj 0) = F := by
      refine Functor.ext ?_ ?_
      · intro j
        have hj : j = 0 := Fin.eq_zero j
        rw [hj]
        rfl
      · intro j k f
        have hj : j = 0 := Fin.eq_zero j
        have hk : k = 0 := Fin.eq_zero k
        subst hj
        subst hk
        have hf : f = 𝟙 (0 : Fin 1) := Subsingleton.elim f _
        rw [hf, Functor.map_id, Functor.map_id]
        simp only [eqToHom_trans, eqToHom_refl, Category.id_comp]
    have hP : (r : PUnit) = PUnit.unit :=
      Subsingleton.elim (α := PUnit) (r : PUnit) PUnit.unit
    cases hP
    exact Sigma.ext hChain HEq.rfl
  right_inv := by
    rintro ⟨X, l⟩
    rfl

@[simp]
theorem replObjZeroEquiv_apply (F : ComposableArrows C 0) (l : L.obj F.left)
    (r : (replUnit C).obj (op F.right)) :
    replObjZeroEquiv L (⟨F, l, r⟩ : replObj C L 0) = ⟨F.obj 0, l⟩ :=
  rfl

@[simp]
theorem replObjZeroEquiv_symm_apply (X : C) (l : L.obj X) :
    (replObjZeroEquiv L).symm (⟨X, l⟩ : Σ X : C, L.obj X) =
      ⟨ComposableArrows.mk₀ X, l, PUnit.unit⟩ :=
  rfl

/-- Elementwise coefficient map for simplicial replacement. -/
def replCoeffMap (α : L ⟶ L') {n : ℕ} :
    replObj C L n → replObj C L' n :=
  barCoeffMap (𝟙 (replUnit C)) α

@[simp]
theorem replCoeffMap_mk (α : L ⟶ L') {n : ℕ} (F : ComposableArrows C n)
    (l : L.obj F.left) (r : (replUnit C).obj (op F.right)) :
    replCoeffMap α (⟨F, l, r⟩ : replObj C L n) =
      (⟨F, α.app F.left l, r⟩ : replObj C L' n) :=
  barCoeffMap_mk _ _ _ _ _

@[simp]
theorem replCoeffMap_chain (α : L ⟶ L') {n : ℕ} (x : replObj C L n) :
    barChain (replCoeffMap α x) = barChain x :=
  barCoeffMap_chain _ _ _

@[simp]
theorem replCoeffMap_coeffL (α : L ⟶ L') {n : ℕ} (x : replObj C L n) :
    barCoeffL (replCoeffMap α x) = α.app (barChain x).left (barCoeffL x) :=
  barCoeffMap_coeffL _ _ _

@[simp]
theorem replCoeffMap_id {n : ℕ} (x : replObj C L n) :
    replCoeffMap (𝟙 L) x = x :=
  barCoeffMap_id x

@[simp]
theorem replCoeffMap_comp {L'' : C ⥤ Type uL} (α : L ⟶ L') (β : L' ⟶ L'')
    {n : ℕ} (x : replObj C L n) :
    replCoeffMap β (replCoeffMap α x) = replCoeffMap (α ≫ β) x := by
  have h := barCoeffMap_comp (𝟙 (replUnit C)) α (𝟙 (replUnit C)) β x
  rwa [Category.id_comp] at h

/-- Packaged data-level coefficient map. -/
def replDataMap (α : L ⟶ L') :
    simplicialReplacementData L ⟶ simplicialReplacementData L' :=
  categoryBarDataMap (𝟙 (replUnit C)) α

@[simp]
theorem replDataMap_app (α : L ⟶ L') (n : ℕ) :
    (replDataMap α).app n = ↾(replCoeffMap α (n := n)) :=
  categoryBarDataMap_app _ _ _

@[simp]
theorem replDataMap_id : replDataMap (𝟙 L) = 𝟙 _ :=
  categoryBarDataMap_id

@[simp]
theorem replDataMap_comp {L'' : C ⥤ Type uL} (α : L ⟶ L') (β : L' ⟶ L'') :
    replDataMap α ≫ replDataMap β = replDataMap (α ≫ β) := by
  have h := categoryBarDataMap_comp (𝟙 (replUnit C)) α (𝟙 (replUnit C)) β
  rwa [Category.id_comp] at h

/-- Packaged simplicial coefficient map. -/
noncomputable def replMap (α : L ⟶ L') :
    simplicialReplacement L ⟶ simplicialReplacement L' :=
  categoryBarMap (𝟙 (replUnit C)) α

@[simp]
theorem replMap_app_mk (α : L ⟶ L') (n : ℕ) :
    (replMap α).app (op (SimplexCategory.mk n)) = ↾(replCoeffMap α (n := n)) :=
  categoryBarMap_app_mk _ _ _

@[simp]
theorem replMap_id : replMap (𝟙 L) = 𝟙 _ :=
  categoryBarMap_id

@[simp]
theorem replMap_comp {L'' : C ⥤ Type uL} (α : L ⟶ L') (β : L' ⟶ L'') :
    replMap α ≫ replMap β = replMap (α ≫ β) := by
  have h := categoryBarMap_comp (𝟙 (replUnit C)) α (𝟙 (replUnit C)) β
  rwa [Category.id_comp] at h

/-- Elementwise indexing-category map for simplicial replacement. -/
def replIdxMap {L' : D ⥤ Type uL} (Φ : C ⥤ D) (α : L ⟶ Φ ⋙ L') {n : ℕ} :
    replObj C L n → replObj D L' n :=
  barIdxMap Φ (replUnitMap Φ) α

@[simp]
theorem replIdxMap_mk {L' : D ⥤ Type uL} (Φ : C ⥤ D) (α : L ⟶ Φ ⋙ L')
    {n : ℕ} (F : ComposableArrows C n) (l : L.obj F.left)
    (r : (replUnit C).obj (op F.right)) :
    replIdxMap Φ α (⟨F, l, r⟩ : replObj C L n) =
      (⟨(Φ.mapComposableArrows n).obj F, α.app F.left l,
        (replUnitMap Φ).app (op F.right) r⟩ : replObj D L' n) :=
  barIdxMap_mk _ _ _ _ _ _

@[simp]
theorem replIdxMap_chain {L' : D ⥤ Type uL} (Φ : C ⥤ D) (α : L ⟶ Φ ⋙ L')
    {n : ℕ} (x : replObj C L n) :
    barChain (replIdxMap Φ α x) = (Φ.mapComposableArrows n).obj (barChain x) :=
  barIdxMap_chain _ _ _ _

@[simp]
theorem replIdxMap_coeffL {L' : D ⥤ Type uL} (Φ : C ⥤ D) (α : L ⟶ Φ ⋙ L')
    {n : ℕ} (x : replObj C L n) :
    barCoeffL (replIdxMap Φ α x) = α.app (barChain x).left (barCoeffL x) :=
  barIdxMap_coeffL _ _ _ _

theorem replIdxMap_chain_nerveMap {L' : D ⥤ Type uL} (Φ : C ⥤ D)
    (α : L ⟶ Φ ⋙ L') {n : ℕ} (x : replObj C L n) :
    barChain (replIdxMap Φ α x) =
      (nerveMap Φ).app (Opposite.op (SimplexCategory.mk n)) (barChain x) :=
  barIdxMap_chain_nerveMap _ _ _ _

/-- The identity `replUnitMap` agrees with the right identity coefficient map. -/
theorem replUnitMap_id : replUnitMap (𝟭 C) = idxIdR := by
  apply NatTrans.ext
  funext X
  rfl

/-- The composite of two `replUnitMap`s agrees with the single composite map. -/
theorem replUnitMap_comp {E : Type u} [Category.{v} E] (Φ : C ⥤ D)
    (Ψ : D ⥤ E) :
    compIdxR Φ Ψ (replUnitMap Φ) (replUnitMap Ψ) = replUnitMap (Φ ⋙ Ψ) := by
  apply NatTrans.ext
  funext X
  exact Category.id_comp _

@[simp]
theorem replIdxMap_id {n : ℕ} (x : replObj C L n) :
    replIdxMap (𝟭 C) idxIdL x = x := by
  have h := barIdxMap_id (R := replUnit C) (L := L) x
  rwa [← replUnitMap_id] at h

@[simp]
theorem replIdxMap_comp {E : Type u} [Category.{v} E] {L' : D ⥤ Type uL}
    {L'' : E ⥤ Type uL} (Φ : C ⥤ D) (Ψ : D ⥤ E) (α : L ⟶ Φ ⋙ L')
    (β : L' ⟶ Ψ ⋙ L'') {n : ℕ} (x : replObj C L n) :
    replIdxMap Ψ β (replIdxMap Φ α x) =
      replIdxMap (Φ ⋙ Ψ) (compIdxL Φ Ψ α β) x := by
  have h := barIdxMap_comp Φ Ψ (replUnitMap Φ) α (replUnitMap Ψ) β x
  rwa [replUnitMap_comp] at h

/-- Packaged data-level indexing-category map. -/
def replIdxDataMap {L' : D ⥤ Type uL} (Φ : C ⥤ D) (α : L ⟶ Φ ⋙ L') :
    simplicialReplacementData L ⟶ simplicialReplacementData L' :=
  categoryBarIdxDataMap Φ (replUnitMap Φ) α

@[simp]
theorem replIdxDataMap_app {L' : D ⥤ Type uL} (Φ : C ⥤ D) (α : L ⟶ Φ ⋙ L')
    (n : ℕ) :
    (replIdxDataMap Φ α).app n = ↾(replIdxMap Φ α (n := n)) :=
  categoryBarIdxDataMap_app _ _ _ _

@[simp]
theorem replIdxDataMap_id : replIdxDataMap (𝟭 C) (idxIdL (L := L)) = 𝟙 _ := by
  have h := categoryBarIdxDataMap_id (R := replUnit C) (L := L)
  rwa [← replUnitMap_id] at h

@[simp]
theorem replIdxDataMap_comp {E : Type u} [Category.{v} E] {L' : D ⥤ Type uL}
    {L'' : E ⥤ Type uL} (Φ : C ⥤ D) (Ψ : D ⥤ E) (α : L ⟶ Φ ⋙ L')
    (β : L' ⟶ Ψ ⋙ L'') :
    replIdxDataMap Φ α ≫ replIdxDataMap Ψ β =
      replIdxDataMap (Φ ⋙ Ψ) (compIdxL Φ Ψ α β) := by
  have h := categoryBarIdxDataMap_comp Φ Ψ (replUnitMap Φ) α (replUnitMap Ψ) β
  rwa [replUnitMap_comp] at h

/-- Packaged simplicial indexing-category map. -/
noncomputable def replIdxMapSSet {L' : D ⥤ Type uL} (Φ : C ⥤ D)
    (α : L ⟶ Φ ⋙ L') :
    simplicialReplacement L ⟶ simplicialReplacement L' :=
  categoryBarIdxMap Φ (replUnitMap Φ) α

@[simp]
theorem replIdxMapSSet_app_mk {L' : D ⥤ Type uL} (Φ : C ⥤ D) (α : L ⟶ Φ ⋙ L')
    (n : ℕ) :
    (replIdxMapSSet Φ α).app (op (SimplexCategory.mk n)) =
      ↾(replIdxMap Φ α (n := n)) :=
  categoryBarIdxMap_app_mk _ _ _ _

@[simp]
theorem replIdxMapSSet_id : replIdxMapSSet (𝟭 C) (idxIdL (L := L)) = 𝟙 _ := by
  have h := categoryBarIdxMap_id (R := replUnit C) (L := L)
  rwa [← replUnitMap_id] at h

@[simp]
theorem replIdxMapSSet_comp {E : Type u} [Category.{v} E] {L' : D ⥤ Type uL}
    {L'' : E ⥤ Type uL} (Φ : C ⥤ D) (Ψ : D ⥤ E) (α : L ⟶ Φ ⋙ L')
    (β : L' ⟶ Ψ ⋙ L'') :
    replIdxMapSSet Φ α ≫ replIdxMapSSet Ψ β =
      replIdxMapSSet (Φ ⋙ Ψ) (compIdxL Φ Ψ α β) := by
  have h := categoryBarIdxMap_comp Φ Ψ (replUnitMap Φ) α (replUnitMap Ψ) β
  rwa [replUnitMap_comp] at h

/-- Mixed naturality, elementwise: coefficient maps commute with index maps. -/
theorem replCoeff_idx_mixed {L₁ L₂ : C ⥤ Type uL} {T₁ T₂ : D ⥤ Type uL}
    (Φ : C ⥤ D) (γ : L₁ ⟶ L₂) (δ : T₁ ⟶ T₂)
    (α : L₁ ⟶ Φ ⋙ T₁) (α' : L₂ ⟶ Φ ⋙ T₂)
    (h : γ ≫ α' = α ≫ Functor.whiskerLeft Φ δ)
    {n : ℕ} (x : replObj C L₁ n) :
    replCoeffMap δ (replIdxMap Φ α x) =
      replIdxMap Φ α' (replCoeffMap γ x) := by
  have hR : (𝟙 (replUnit C)) ≫ replUnitMap Φ =
      replUnitMap Φ ≫ Functor.whiskerLeft Φ.op (𝟙 (replUnit D)) := by
    apply NatTrans.ext
    funext X
    rfl
  exact barCoeff_idx_mixed Φ (𝟙 (replUnit C)) γ (𝟙 (replUnit D)) δ
    (replUnitMap Φ) α (replUnitMap Φ) α' hR h x

/-- Mixed naturality at the `Data` level. -/
theorem replDataMap_idx_mixed {L₁ L₂ : C ⥤ Type uL} {T₁ T₂ : D ⥤ Type uL}
    (Φ : C ⥤ D) (γ : L₁ ⟶ L₂) (δ : T₁ ⟶ T₂)
    (α : L₁ ⟶ Φ ⋙ T₁) (α' : L₂ ⟶ Φ ⋙ T₂)
    (h : γ ≫ α' = α ≫ Functor.whiskerLeft Φ δ) :
    replIdxDataMap Φ α ≫ replDataMap δ =
      replDataMap γ ≫ replIdxDataMap Φ α' := by
  have hR : (𝟙 (replUnit C)) ≫ replUnitMap Φ =
      replUnitMap Φ ≫ Functor.whiskerLeft Φ.op (𝟙 (replUnit D)) := by
    apply NatTrans.ext
    funext X
    rfl
  exact categoryBarDataMap_idx_mixed Φ (𝟙 (replUnit C)) γ (𝟙 (replUnit D)) δ
    (replUnitMap Φ) α (replUnitMap Φ) α' hR h

/-- Mixed naturality at the simplicial-set level. -/
theorem replMap_idx_mixed {L₁ L₂ : C ⥤ Type uL} {T₁ T₂ : D ⥤ Type uL}
    (Φ : C ⥤ D) (γ : L₁ ⟶ L₂) (δ : T₁ ⟶ T₂)
    (α : L₁ ⟶ Φ ⋙ T₁) (α' : L₂ ⟶ Φ ⋙ T₂)
    (h : γ ≫ α' = α ≫ Functor.whiskerLeft Φ δ) :
    replIdxMapSSet Φ α ≫ replMap δ =
      replMap γ ≫ replIdxMapSSet Φ α' := by
  have hR : (𝟙 (replUnit C)) ≫ replUnitMap Φ =
      replUnitMap Φ ≫ Functor.whiskerLeft Φ.op (𝟙 (replUnit D)) := by
    apply NatTrans.ext
    funext X
    rfl
  exact categoryBarMap_idx_mixed Φ (𝟙 (replUnit C)) γ (𝟙 (replUnit D)) δ
    (replUnitMap Φ) α (replUnitMap Φ) α' hR h

end CategoryBar

end CategoryTheory
