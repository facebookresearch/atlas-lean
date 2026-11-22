/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.SimplicialReplacement
public import MathlibExt.CategoryTheory.NerveData

/-!
# Simplicial replacement versus the nerve of the category of elements

For `C : Type u` with `Category.{v} C` and `L : C ⥤ Type uL`, the degree-`n`
simplicial replacement object `replObj C L n` is equivalent to
`ComposableArrows L.Elements n`.

Chain orientation: `L` sits at `F.left` (source endpoint, covariant). The forward
map sends `⟨F, l, _⟩` to the chain over `L.Elements` whose vertex at `i` is
`⟨F.obj i, L.map (F.map (0 ≤ i)) l⟩`; the inverse projects along
`Functor.Elements.π L` and remembers the element over the source vertex.

References (orientation only; no exact proposition correspondence is claimed):
nLab `category of elements` page
(https://ncatlab.org/nlab/show/category+of+elements); Thomason, *Homotopy colimits
in the category of small categories*
(https://doi.org/10.1017/S0305004100055535), for the replacement/Grothendieck
background.

Source-to-Lean map: the classical category of elements of `L` is Mathlib's
`L.Elements` (`Functor.Elements`); simplicial replacement `replObj C L n`
compares via `replElementsEquiv` against `ComposableArrows L.Elements n`.

Nonclaims: this packet contains no
comma/Grothendieck/opposite/reversal comparison.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v uL

namespace CategoryTheory

namespace CategoryBar

variable {C : Type u} [Category.{v} C]
variable {L : C ⥤ Type uL}
variable {n : ℕ}

/-- Degreewise equivalence between simplicial replacement and the nerve of the
category of elements, with `L` at the source endpoint. -/
def replElementsEquiv (C : Type u) [Category.{v} C]
    (L : C ⥤ Type uL) (n : ℕ) :
    replObj C L n ≃ ComposableArrows L.Elements n where
  toFun
    | ⟨F, l, _⟩ =>
      { obj := fun i => L.elementsMk (F.obj i) (L.map (F.map' 0 i.val) l)
        map := fun {i j} f =>
          Functor.Elements.homMk (F.map f) (by
            change L.map (F.map f) (L.map (F.map' 0 i.val) l) =
              L.map (F.map' 0 j.val) l
            have hC : F.map' 0 i.val ≫ F.map f = F.map' 0 j.val := by
              rw [← F.map_comp]
              congr 1
            rw [← Functor.map_comp_apply, hC])
        map_id := fun i => by
          apply Functor.Elements.hom_ext
          change F.map (𝟙 i) = 𝟙 (F.obj i)
          exact F.map_id i
        map_comp := fun f g => by
          apply Functor.Elements.hom_ext
          change F.map (f ≫ g) = F.map f ≫ F.map g
          exact F.map_comp f g }
  invFun G :=
    ⟨G ⋙ Functor.Elements.π L, (G.obj ⟨0, Nat.succ_pos n⟩).val, PUnit.unit⟩
  left_inv := by
    rintro ⟨F, l, r⟩
    have hCoeff : L.map (F.map' 0 0) l = l := by
      rw [F.map'_self 0, L.map_id]
      rfl
    have hP : (r : PUnit) = PUnit.unit :=
      Subsingleton.elim (α := PUnit) (r : PUnit) PUnit.unit
    cases hP
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact Prod.ext hCoeff rfl
  right_inv := by
    intro G
    refine Functor.ext (fun i => ?_) (fun i j f => ?_)
    · refine Functor.Elements.ext _ _ ?_ ?_
      · rfl
      change L.map (eqToHom rfl)
          (L.map (ComposableArrows.map' (G ⋙ Functor.Elements.π L) 0 i.val)
            (G.obj ⟨0, Nat.succ_pos n⟩).val) = (G.obj i).val
      rw [eqToHom_refl, L.map_id]
      have hval :
          (ComposableArrows.map' (G ⋙ Functor.Elements.π L) 0 i.val) =
            (G.map' 0 i.val).hom :=
        rfl
      rw [hval]
      exact (G.map' 0 i.val).map_val
    · apply Functor.Elements.hom_ext
      have hEq : ∀ {x y : L.Elements} (h : x = y),
          (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
        intro x y h
        cases h
        rfl
      rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom, hEq, hEq]
      change ((G ⋙ Functor.Elements.π L).map f) = 𝟙 _ ≫ (G.map f).hom ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      rfl

@[simp]
theorem replElementsEquiv_apply (F : ComposableArrows C n) (l : L.obj F.left)
    (r : (replUnit C).obj (op F.right)) (i : Fin (n + 1)) :
    (((replElementsEquiv (C := C) (L := L) n) ⟨F, l, r⟩).obj i).obj = F.obj i :=
  rfl

@[simp]
theorem replElementsEquiv_symm_apply (G : ComposableArrows L.Elements n) :
    (replElementsEquiv (C := C) (L := L) n).symm G =
      ⟨G ⋙ Functor.Elements.π L, (G.obj ⟨0, Nat.succ_pos n⟩).val, PUnit.unit⟩ :=
  rfl

/-- The elements-nerve comparison preserves every degeneracy. -/
theorem replNerve_degeneracy {n : ℕ} (i : Fin (n + 1))
    (x : replObj C L n) :
    (nerve L.Elements).σ i (replElementsEquiv C L n x) =
      replElementsEquiv C L (n + 1) (barσ i x) := by
  obtain ⟨F, l, r⟩ := x
  refine Functor.ext (fun j => ?_) (fun j k f => ?_)
  · refine Functor.Elements.ext _ _ rfl ?_
    change
      L.map (eqToHom rfl)
        (((nerve L.Elements).σ i
          ((replElementsEquiv C L n) ⟨F, l, r⟩)).obj j).val =
        (((replElementsEquiv C L (n + 1))
          (barσ (R := replUnit C) (L := L) i ⟨F, l, r⟩)).obj j).val
    rw [eqToHom_refl, L.map_id]
    rfl
  · apply Functor.Elements.hom_ext
    have hEq : ∀ {x y : L.Elements} (h : x = y),
        (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
      intro x y h
      cases h
      rfl
    rw [Functor.Elements.comp_hom]
    rw [Functor.Elements.comp_hom, hEq, hEq]
    change
      ((((nerve L.Elements).σ i
        ((replElementsEquiv C L n) ⟨F, l, r⟩)) ⋙
        Functor.Elements.π L).map f) =
        𝟙 _ ≫
          ((((replElementsEquiv C L (n + 1))
            (barσ (R := replUnit C) (L := L) i ⟨F, l, r⟩)) ⋙
            Functor.Elements.π L).map f) ≫
          𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    rfl

/-- The elements-nerve comparison preserves the last face. -/
theorem replNerve_face_last {n : ℕ} (x : replObj C L (n + 1)) :
    (nerve L.Elements).δ (Fin.last (n + 1))
        (replElementsEquiv C L (n + 1) x) =
      replElementsEquiv C L n (barδ (Fin.last (n + 1)) x) := by
  obtain ⟨F, l, r⟩ := x
  have h := barδ_last_eq (R := replUnit C) (L := L) (n := n) ⟨F, l, r⟩
  rw [h]
  dsimp only
  refine Functor.ext (fun j => ?_) (fun j k f => ?_)
  · simp only [CategoryTheory.nerve.δ_obj]
    have hSucc : (Fin.last (n + 1)).succAbove j = j.castSucc :=
      congrFun Fin.succAbove_last j
    rw [hSucc]
    refine Functor.Elements.ext _ _ (congrArg F.obj hSucc.symm) ?_
    have eX : ((((replElementsEquiv C L (n + 1)) ⟨F, l, r⟩).obj j.castSucc).val) =
        L.map (F.map' 0 (j.castSucc).val) l := rfl
    have hComb : L.map (eqToHom (congrArg F.obj hSucc.symm))
          (L.map (F.map' 0 (j.castSucc).val) l) =
        L.map ((F.map' 0 (j.castSucc).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) l := by
      rw [Functor.map_comp]
      rfl
    have eMor : ((F.map' 0 (j.castSucc).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) =
        (((nerve C).δ (Fin.last (n + 1)) F).map' 0 j.val) := by
      simp only [ComposableArrows.map', SimplicialObject.δ_def, nerve,
        ComposableArrows.whiskerLeft, ConcreteCategory.hom]
      have hEq : eqToHom (congrArg F.obj hSucc.symm) = F.map (eqToHom hSucc.symm) :=
        (eqToHom_map F hSucc.symm).symm
      simp only [hEq, ← F.map_comp]
      exact congrArg (F.map ·) (Subsingleton.elim _ _)
    exact Eq.trans (congrArg (L.map (eqToHom (congrArg F.obj hSucc.symm))) eX)
      (Eq.trans hComb (congrArg (fun m => L.map m l) eMor))
  · apply Functor.Elements.hom_ext
    have hEq : ∀ {x y : L.Elements} (h : x = y),
        (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
      intro x y h
      cases h
      rfl
    rw [Functor.Elements.comp_hom]
    rw [Functor.Elements.comp_hom, hEq, hEq]
    have gen : ∀ {uj uk vj vk : Fin (n + 2)} (s₁ : uj = vj) (s₂ : vk = uk)
        (e₁ : F.obj uj = F.obj vj) (e₂ : F.obj vk = F.obj uk)
        (uf : uj ⟶ uk) (vf : vj ⟶ vk),
        F.map uf = eqToHom e₁ ≫ F.map vf ≫ eqToHom e₂ := by
      intro uj uk vj vk s₁ s₂ e₁ e₂ uf vf
      have q₁ : eqToHom e₁ = F.map (eqToHom s₁) := (eqToHom_map F s₁).symm
      have q₂ : eqToHom e₂ = F.map (eqToHom s₂) := (eqToHom_map F s₂).symm
      rw [q₁, q₂, ← F.map_comp, ← F.map_comp]
      exact congrArg (F.map ·) (Subsingleton.elim _ _)
    exact gen rfl rfl _ _
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ (Fin.last (n + 1))).op.unop).toFunctor.map f)
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ (Fin.last (n + 1))).op.unop).toFunctor.map f)

/-- The elements-nerve comparison preserves the first face. -/
theorem replNerve_face_zero {n : ℕ} (x : replObj C L (n + 1)) :
    (nerve L.Elements).δ (0 : Fin (n + 2))
        (replElementsEquiv C L (n + 1) x) =
      replElementsEquiv C L n (barδ (0 : Fin (n + 2)) x) := by
  obtain ⟨F, l, r⟩ := x
  have h := barδ_zero_eq (R := replUnit C) (L := L) (n := n) ⟨F, l, r⟩
  rw [h]
  dsimp only
  refine Functor.ext (fun j => ?_) (fun j k f => ?_)
  · simp only [CategoryTheory.nerve.δ_obj]
    have hSucc : (0 : Fin (n + 2)).succAbove j = j.succ :=
      congrFun Fin.succAbove_zero j
    rw [hSucc]
    refine Functor.Elements.ext _ _ (congrArg F.obj hSucc.symm) ?_
    have hj_le : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have hsucc_val : (j.succ).val = j.val + 1 := rfl
    have h1_le_succ : 1 ≤ (j.succ).val := by
      rw [hsucc_val]; exact Nat.succ_le_succ (Nat.zero_le _)
    have hsucc_le : (j.succ).val ≤ n + 1 := by
      rw [hsucc_val]; exact Nat.succ_le_succ hj_le
    have eX : ((((replElementsEquiv C L (n + 1)) ⟨F, l, r⟩).obj j.succ).val) =
        L.map (F.map' 0 (j.succ).val) l := rfl
    have hComb : L.map (eqToHom (congrArg F.obj hSucc.symm))
          (L.map (F.map' 0 (j.succ).val) l) =
        L.map ((F.map' 0 (j.succ).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) l := by
      rw [Functor.map_comp]
      rfl
    have hCombR : L.map ((((nerve C).δ (0 : Fin (n + 2)) F).map' 0 j.val))
          (L.map (F.map' 0 1) l) =
        L.map ((F.map' 0 1) ≫ (((nerve C).δ (0 : Fin (n + 2)) F).map' 0 j.val)) l := by
      have hmc := Functor.map_comp L (F.map' 0 1)
        ((((nerve C).δ (0 : Fin (n + 2)) F).map' 0 j.val))
      have h2 := congrArg (fun f => f l) hmc
      exact h2.symm
    have hFuse : F.map' 0 (j.succ).val = F.map' 0 1 ≫ F.map' 1 (j.succ).val := by
      have hcomp := F.map'_comp 0 1 (j.succ).val (Nat.zero_le 1) h1_le_succ hsucc_le
      exact hcomp
    have eSingle : ((F.map' 1 (j.succ).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) =
        (((nerve C).δ (0 : Fin (n + 2)) F).map' 0 j.val) := by
      simp only [ComposableArrows.map', SimplicialObject.δ_def, nerve,
        ComposableArrows.whiskerLeft, ConcreteCategory.hom]
      have hEq : eqToHom (congrArg F.obj hSucc.symm) = F.map (eqToHom hSucc.symm) :=
        (eqToHom_map F hSucc.symm).symm
      simp only [hEq, ← F.map_comp]
      exact congrArg (F.map ·) (Subsingleton.elim _ _)
    have eMor : ((F.map' 0 (j.succ).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) =
        ((F.map' 0 1) ≫ (((nerve C).δ (0 : Fin (n + 2)) F).map' 0 j.val)) :=
      Eq.trans (congrArg (· ≫ eqToHom (congrArg F.obj hSucc.symm)) hFuse)
        (Eq.trans (Category.assoc _ _ _)
          (congrArg ((F.map' 0 1) ≫ ·) eSingle))
    have eY : (((replElementsEquiv C L n)
          ⟨(nerve C).δ (0 : Fin (n + 2)) F,
            (cast (congrArg L.obj (rfl : F.obj' 1 = ((nerve C).δ (0 : Fin (n + 2)) F).left))
              (L.map (F.map' 0 1) l)), cast (congrArg (fun Z => (replUnit C).obj (op Z)) (by
                change F.obj ⟨n + 1, by omega⟩ =
                  ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _)
                rw [CategoryTheory.nerve.δ_obj]
                rfl)) r⟩).obj j).val =
        L.map ((((nerve C).δ (0 : Fin (n + 2)) F).map' 0 j.val)) (L.map (F.map' 0 1) l) := rfl
    exact Eq.trans (congrArg (L.map (eqToHom (congrArg F.obj hSucc.symm))) eX)
      (Eq.trans hComb
        (Eq.trans (congrArg (fun m => L.map m l) eMor)
          (Eq.trans hCombR.symm eY.symm)))
  · apply Functor.Elements.hom_ext
    have hEq : ∀ {x y : L.Elements} (h : x = y),
        (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
      intro x y h
      cases h
      rfl
    rw [Functor.Elements.comp_hom]
    rw [Functor.Elements.comp_hom, hEq, hEq]
    have gen : ∀ {uj uk vj vk : Fin (n + 2)} (s₁ : uj = vj) (s₂ : vk = uk)
        (e₁ : F.obj uj = F.obj vj) (e₂ : F.obj vk = F.obj uk)
        (uf : uj ⟶ uk) (vf : vj ⟶ vk),
        F.map uf = eqToHom e₁ ≫ F.map vf ≫ eqToHom e₂ := by
      intro uj uk vj vk s₁ s₂ e₁ e₂ uf vf
      have q₁ : eqToHom e₁ = F.map (eqToHom s₁) := (eqToHom_map F s₁).symm
      have q₂ : eqToHom e₂ = F.map (eqToHom s₂) := (eqToHom_map F s₂).symm
      rw [q₁, q₂, ← F.map_comp, ← F.map_comp]
      exact congrArg (F.map ·) (Subsingleton.elim _ _)
    exact gen rfl rfl _ _
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op.unop).toFunctor.map f)
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op.unop).toFunctor.map f)

/-- The elements-nerve comparison preserves every interior face. -/
theorem replNerve_face_interior {n : ℕ} (q : Fin n) (x : replObj C L (n + 1)) :
    (nerve L.Elements).δ q.castSucc.succ
        (replElementsEquiv C L (n + 1) x) =
      replElementsEquiv C L n (barδ q.castSucc.succ x) := by
  obtain ⟨F, l, r⟩ := x
  have h := barδ_castSucc_succ_eq (R := replUnit C) (L := L) (n := n) q ⟨F, l, r⟩
  rw [h]
  dsimp only
  refine Functor.ext (fun j => ?_) (fun j k f => ?_)
  · simp only [CategoryTheory.nerve.δ_obj]
    by_cases hle : j ≤ q.castSucc
    · have hSucc : q.castSucc.succ.succAbove j = j.castSucc :=
        Fin.succAbove_succ_of_le _ _ hle
      rw [hSucc]
      refine Functor.Elements.ext _ _ (congrArg F.obj hSucc.symm) ?_
      have eX : ((((replElementsEquiv C L (n + 1)) ⟨F, l, r⟩).obj j.castSucc).val) =
          L.map (F.map' 0 (j.castSucc).val) l := rfl
      have hComb : L.map (eqToHom (congrArg F.obj hSucc.symm))
            (L.map (F.map' 0 (j.castSucc).val) l) =
          L.map ((F.map' 0 (j.castSucc).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) l := by
        rw [Functor.map_comp]
        rfl
      have eMor : ((F.map' 0 (j.castSucc).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) =
          (((nerve C).δ q.castSucc.succ F).map' 0 j.val) := by
        simp only [ComposableArrows.map', SimplicialObject.δ_def, nerve,
          ComposableArrows.whiskerLeft, ConcreteCategory.hom]
        have hEq : eqToHom (congrArg F.obj hSucc.symm) = F.map (eqToHom hSucc.symm) :=
          (eqToHom_map F hSucc.symm).symm
        simp only [hEq, ← F.map_comp]
        exact congrArg (F.map ·) (Subsingleton.elim _ _)
      exact Eq.trans (congrArg (L.map (eqToHom (congrArg F.obj hSucc.symm))) eX)
        (Eq.trans hComb (congrArg (fun m => L.map m l) eMor))
    · have hlt : q.castSucc < j := lt_of_not_ge hle
      have hSucc : q.castSucc.succ.succAbove j = j.succ :=
        Fin.succAbove_succ_of_lt _ _ hlt
      rw [hSucc]
      refine Functor.Elements.ext _ _ (congrArg F.obj hSucc.symm) ?_
      have eX : ((((replElementsEquiv C L (n + 1)) ⟨F, l, r⟩).obj j.succ).val) =
          L.map (F.map' 0 (j.succ).val) l := rfl
      have hComb : L.map (eqToHom (congrArg F.obj hSucc.symm))
            (L.map (F.map' 0 (j.succ).val) l) =
          L.map ((F.map' 0 (j.succ).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) l := by
        rw [Functor.map_comp]
        rfl
      have eMor : ((F.map' 0 (j.succ).val) ≫ eqToHom (congrArg F.obj hSucc.symm)) =
          (((nerve C).δ q.castSucc.succ F).map' 0 j.val) := by
        simp only [ComposableArrows.map', SimplicialObject.δ_def, nerve,
          ComposableArrows.whiskerLeft, ConcreteCategory.hom]
        have hEq : eqToHom (congrArg F.obj hSucc.symm) = F.map (eqToHom hSucc.symm) :=
          (eqToHom_map F hSucc.symm).symm
        simp only [hEq, ← F.map_comp]
        exact congrArg (F.map ·) (Subsingleton.elim _ _)
      exact Eq.trans (congrArg (L.map (eqToHom (congrArg F.obj hSucc.symm))) eX)
        (Eq.trans hComb (congrArg (fun m => L.map m l) eMor))
  · apply Functor.Elements.hom_ext
    have hEq : ∀ {x y : L.Elements} (h : x = y),
        (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
      intro x y h
      cases h
      rfl
    rw [Functor.Elements.comp_hom]
    rw [Functor.Elements.comp_hom, hEq, hEq]
    have gen : ∀ {uj uk vj vk : Fin (n + 2)} (s₁ : uj = vj) (s₂ : vk = uk)
        (e₁ : F.obj uj = F.obj vj) (e₂ : F.obj vk = F.obj uk)
        (uf : uj ⟶ uk) (vf : vj ⟶ vk),
        F.map uf = eqToHom e₁ ≫ F.map vf ≫ eqToHom e₂ := by
      intro uj uk vj vk s₁ s₂ e₁ e₂ uf vf
      have q₁ : eqToHom e₁ = F.map (eqToHom s₁) := (eqToHom_map F s₁).symm
      have q₂ : eqToHom e₂ = F.map (eqToHom s₂) := (eqToHom_map F s₂).symm
      rw [q₁, q₂, ← F.map_comp, ← F.map_comp]
      exact congrArg (F.map ·) (Subsingleton.elim _ _)
    exact gen rfl rfl _ _
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ q.castSucc.succ).op.unop).toFunctor.map f)
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ q.castSucc.succ).op.unop).toFunctor.map f)

/-- The elements-nerve comparison preserves every face. -/
theorem replNerve_face_compat {n : ℕ} (i : Fin (n + 2))
    (x : replObj C L (n + 1)) :
    (nerve L.Elements).δ i (replElementsEquiv C L (n + 1) x) =
      replElementsEquiv C L n (barδ i x) := by
  by_cases h0 : i.val = 0
  · have hi0 : i = 0 := Fin.ext h0
    subst hi0
    exact replNerve_face_zero x
  · by_cases hL : i.val = n + 1
    · have hiL : i = Fin.last (n + 1) := by
        apply Fin.ext
        rw [hL]
        simp [Fin.val_last]
      subst hiL
      exact replNerve_face_last x
    · obtain ⟨q, hk⟩ : ∃ q : Fin n, i.val = q.val + 1 :=
        ⟨⟨i.val - 1, by omega⟩, by change i.val = i.val - 1 + 1; omega⟩
      have hi : i = q.castSucc.succ := by
        apply Fin.ext
        simp [Fin.val_succ, Fin.val_castSucc, hk]
      subst hi
      exact replNerve_face_interior q x

/-- The degreewise comparison commutes with every degeneracy. -/
theorem replNerve_degeneracy_compat {n : ℕ} (i : Fin (n + 1)) :
    (Equiv.toIso (replElementsEquiv C L n)).hom ≫
        (nerveData L.Elements).σ i =
      (simplicialReplacementData L).σ i ≫
        (Equiv.toIso (replElementsEquiv C L (n + 1))).hom := by
  ext x
  change (nerve L.Elements).σ i (replElementsEquiv C L n x) =
    replElementsEquiv C L (n + 1) (barσ i x)
  exact replNerve_degeneracy i x

/-- Simplicial Data isomorphism between replacement and the elements nerve. -/
noncomputable def replNerveDataIso (L : C ⥤ Type uL) :
    simplicialReplacementData L ≅ nerveData L.Elements :=
  SimplicialObject.Data.isoOfIso
    (fun n => Equiv.toIso (replElementsEquiv C L n))
    (fun {n} i => by
      ext x
      change (nerve L.Elements).δ i (replElementsEquiv C L (n + 1) x) =
        replElementsEquiv C L n (barδ i x)
      exact replNerve_face_compat i x)
    (fun i => replNerve_degeneracy_compat i)

/-- Simplicial-set isomorphism between replacement and the elements nerve. -/
noncomputable def replNerveSimplicialIso (L : C ⥤ Type uL) :
    simplicialReplacement L ≅ nerve L.Elements :=
  (SimplicialObject.Data.toSimplicialFunctor.mapIso (replNerveDataIso L)).trans
    (nerveDataSimplicialIso (C := L.Elements))

end CategoryBar

end CategoryTheory
