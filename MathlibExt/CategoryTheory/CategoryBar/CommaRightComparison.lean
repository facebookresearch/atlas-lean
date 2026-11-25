/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.CommaRightElements
public import MathlibExt.CategoryTheory.CategoryBar.NerveComparison

/-!
# Right-comma degreewise bar comparison

For `F : C ⥤ D` and `d : D`, the degree-`n` bar object at the right-comma
coefficient `commaCoeffR F d` with unit left coefficient is equivalent to
`ComposableArrows (CostructuredArrow F d) n`. The forward map sends `x` to the
composable arrow whose `i`-th object is
`CostructuredArrow.mk (F.map ((barChain x).map' i.val n) ≫ barCoeffR x)`;
the inverse projects the chain and reads the comma arrow at the last vertex.

The degreewise equivalences assemble into a simplicial `Data` isomorphism and
hence a simplicial-set isomorphism with the comma-category nerve.

References (orientation only; no exact proposition correspondence is claimed):
nLab `comma category` page (https://ncatlab.org/nlab/show/comma+category);
Thomason, *Homotopy colimits in the category of small categories*
(https://doi.org/10.1017/S0305004100055535), for comma-fibre background.

Source-to-Lean map: the classical right comma category `F ↓ d` is Mathlib's
`CostructuredArrow F d`; the representable coefficient is `commaCoeffR F d`,
and the bar at it compares via the degreewise `barRightCommaEquiv` against
`nerve (CostructuredArrow F d)`.

Nonclaims: no naturality, no contraction, no homotopy, no realization, and no KQ result.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace CategoryBar

/-- Degreewise equivalence between the right-comma bar and comma arrows.

The forward map pairs the underlying chain with postcomposed comma arrows;
the inverse projects the chain and reads the comma arrow at the last vertex. -/
noncomputable def barRightCommaEquiv
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) (n : ℕ) :
    barObj C (commaCoeffR F d) (unitCoeffL C) n ≃
      ComposableArrows (CostructuredArrow F d) n where
  toFun x :=
    { obj := fun i => CostructuredArrow.mk (F.map (x.1.map' i.val n) ≫ x.2.2)
      map := fun {i j} f => CostructuredArrow.homMk (x.1.map f) (by
        obtain ⟨G, l, (h : F.obj G.right ⟶ d)⟩ := x
        change F.map (G.map f) ≫ (F.map (G.map' j.val n) ≫ h) =
          F.map (G.map' i.val n) ≫ h
        have hsq : G.map f ≫ G.map' j.val n = G.map' i.val n := by
          rw [← G.map_comp]
          congr 1
        rw [← Category.assoc, ← F.map_comp, hsq])
      map_id := fun i => by
        apply CostructuredArrow.hom_ext _ _
        exact x.1.map_id _
      map_comp := fun f g => by
        apply CostructuredArrow.hom_ext _ _
        exact x.1.map_comp _ _ }
  invFun Y :=
    ⟨Y ⋙ CostructuredArrow.proj F d, ULift.up PUnit.unit,
      CostructuredArrow.hom (Y.obj (Fin.last n))⟩
  left_inv := by
    rintro ⟨G, l, (h : F.obj G.right ⟶ d)⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    have hL : Subsingleton ((unitCoeffL C).obj G.left) := by
      change Subsingleton (ULift.{0} PUnit)
      infer_instance
    refine Prod.ext (@Subsingleton.elim _ hL _ _) ?_
    change F.map (G.map' n n) ≫ h = h
    rw [G.map'_self n, F.map_id, Category.id_comp]
  right_inv := by
    intro Y
    refine Functor.ext (fun i => ?_) (fun i j f => ?_)
    · change CostructuredArrow.mk
          (F.map (ComposableArrows.map' (Y ⋙ CostructuredArrow.proj F d) i.val n) ≫
            CostructuredArrow.hom (Y.obj (Fin.last n))) = Y.obj i
      have hl : (CostructuredArrow.mk
          (F.map (ComposableArrows.map' (Y ⋙ CostructuredArrow.proj F d) i.val n) ≫
            CostructuredArrow.hom (Y.obj (Fin.last n)))).left = (Y.obj i).left :=
        rfl
      refine CostructuredArrow.obj_ext _ _ hl ?_
      have hw : (Y.obj i).hom =
          F.map (ComposableArrows.map' (Y ⋙ CostructuredArrow.proj F d) i.val n) ≫
            CostructuredArrow.hom (Y.obj (Fin.last n)) :=
        (CostructuredArrow.w (Y.map' i.val n)).symm
      have r1 : eqToHom hl = 𝟙 _ := eqToHom_refl _ hl
      have r2 : F.map (eqToHom hl) = 𝟙 _ :=
        (congrArg F.map r1).trans (F.map_id _)
      have e1 : F.map (eqToHom hl) ≫ (Y.obj i).hom = (Y.obj i).hom :=
        (congrArg (· ≫ (Y.obj i).hom) r2).trans (Category.id_comp _)
      exact e1.trans hw
    · apply CostructuredArrow.hom_ext _ _
      have hEq : ∀ {x y : CostructuredArrow F d} (h : x = y),
          (eqToHom h).left = eqToHom (congrArg CostructuredArrow.left h) := by
        intro x y h
        cases h
        rfl
      rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, hEq, hEq]
      change (Y.map f).left = 𝟙 _ ≫ (Y.map f).left ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]

/-- The left projection of the forward comma arrow is the chain object. -/
@[simp] theorem barRightCommaEquiv_apply_left
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) (n : ℕ)
    (x : barObj C (commaCoeffR F d) (unitCoeffL C) n) (i : Fin (n + 1)) :
    (((barRightCommaEquiv F d n) x).obj i).left = (barChain x).obj i :=
  rfl

/-- The inverse is the chain projection with the last-vertex comma arrow. -/
@[simp] theorem barRightCommaEquiv_symm_apply
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) (n : ℕ)
    (Y : ComposableArrows (CostructuredArrow F d) n) :
    (barRightCommaEquiv F d n).symm Y =
      ⟨Y ⋙ CostructuredArrow.proj F d, ULift.up PUnit.unit,
        CostructuredArrow.hom (Y.obj (Fin.last n))⟩ :=
  rfl

/-- Zero-face compatibility for the right-comma comparison.

The right endpoint is fixed by `d₀`, so the comma arrow needs no fusion:
the shortened tail is directly the original tail past `j.succ`. -/
theorem barRightComma_face_zero {n : ℕ}
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D)
    (x : barObj C (commaCoeffR F d) (unitCoeffL C) (n + 1)) :
    (nerve (CostructuredArrow F d)).δ (0 : Fin (n + 2))
        (barRightCommaEquiv F d (n + 1) x) =
      barRightCommaEquiv F d n (barδ (0 : Fin (n + 2)) x) := by
  obtain ⟨G, l, h⟩ := x
  have hbar :=
    barδ_zero_eq (R := commaCoeffR F d) (L := unitCoeffL C) (n := n) ⟨G, l, h⟩
  rw [hbar]
  dsimp only
  refine Functor.ext (fun (j : Fin (n + 1)) => ?_) (fun j k f => ?_)
  · simp only [CategoryTheory.nerve.δ_obj]
    have hSucc : (0 : Fin (n + 2)).succAbove j = j.succ :=
      congrFun Fin.succAbove_zero j
    rw [hSucc]
    refine CostructuredArrow.obj_ext _ _ (congrArg G.obj hSucc.symm) ?_
    change F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫
          (F.map ((((nerve C).δ (0 : Fin (n + 2)) G).map' j.val n)) ≫ h) =
        F.map (G.map' (j.succ).val (n + 1)) ≫ h
    have hComb : F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫
          (F.map ((((nerve C).δ (0 : Fin (n + 2)) G).map' j.val n)) ≫ h) =
        F.map ((eqToHom (congrArg G.obj hSucc.symm)) ≫
          (((nerve C).δ (0 : Fin (n + 2)) G).map' j.val n)) ≫ h :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ h) (F.map_comp _ _).symm)
    have hEq : eqToHom (congrArg G.obj hSucc.symm) =
        G.map (eqToHom hSucc.symm) :=
      (eqToHom_map G hSucc.symm).symm
    have eMor : ((eqToHom (congrArg G.obj hSucc.symm)) ≫
          (((nerve C).δ (0 : Fin (n + 2)) G).map' j.val n)) =
        (G.map' (j.succ).val (n + 1)) := by
      rw [hEq]
      change G.map (eqToHom hSucc.symm) ≫ G.map _ = G.map _
      exact (G.map_comp _ _).symm.trans
        (congrArg (G.map ·) (Subsingleton.elim _ _))
    exact hComb.trans (congrArg (fun m => F.map m ≫ h) eMor)
  · apply CostructuredArrow.hom_ext _ _
    have hEq : ∀ {x y : CostructuredArrow F d} (hh : x = y),
        (eqToHom hh).left = eqToHom (congrArg CostructuredArrow.left hh) := by
      intro x y hh
      cases hh
      rfl
    rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, hEq, hEq]
    have gen : ∀ {uj uk vj vk : Fin (n + 2)} (s₁ : uj = vj) (s₂ : vk = uk)
        (e₁ : G.obj uj = G.obj vj) (e₂ : G.obj vk = G.obj uk)
        (uf : uj ⟶ uk) (vf : vj ⟶ vk),
        G.map uf = eqToHom e₁ ≫ G.map vf ≫ eqToHom e₂ := by
      intro uj uk vj vk s₁ s₂ e₁ e₂ uf vf
      have q₁ : eqToHom e₁ = G.map (eqToHom s₁) := (eqToHom_map G s₁).symm
      have q₂ : eqToHom e₂ = G.map (eqToHom s₂) := (eqToHom_map G s₂).symm
      rw [q₁, q₂, ← G.map_comp, ← G.map_comp]
      exact congrArg (G.map ·) (Subsingleton.elim _ _)
    exact gen rfl rfl _ _
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op.unop).toFunctor.map f)
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op.unop).toFunctor.map f)

/-- Interior-face compatibility for the right-comma comparison.

Both endpoints are fixed by an interior face, so each branch closes by the
corresponding `Fin.succAbove_succ_of_le/of_lt` identification with no
coefficient fusion. -/
theorem barRightComma_face_interior {n : ℕ} (q : Fin n)
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D)
    (x : barObj C (commaCoeffR F d) (unitCoeffL C) (n + 1)) :
    (nerve (CostructuredArrow F d)).δ q.castSucc.succ
        (barRightCommaEquiv F d (n + 1) x) =
      barRightCommaEquiv F d n (barδ q.castSucc.succ x) := by
  obtain ⟨G, l, h⟩ := x
  let hR : F.obj G.right ⟶ d := h
  have hbar :=
    barδ_castSucc_succ_eq (R := commaCoeffR F d) (L := unitCoeffL C) (n := n) q
      ⟨G, l, h⟩
  have hne : q.castSucc.succ ≠ Fin.last (n + 1) := by
    apply ne_of_apply_ne Fin.val
    rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    have hq := q.isLt
    omega
  have sP : q.castSucc.succ.succAbove (Fin.last n) = Fin.last (n + 1) :=
    Fin.succAbove_ne_last_last hne
  have hcast' : ∀ {X Y : C} (e : X = Y) (k : F.obj X ⟶ d),
      cast (congrArg (fun Z => F.obj Z ⟶ d) e) k =
        F.map (eqToHom e.symm) ≫ k := by
    intro X Y e k
    subst e
    simp
  have hcastW : ∀ {X Y : C} (e : X = Y) (k : (commaCoeffR F d).obj (op X)),
      cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) e) k =
        cast (commaCoeffR_obj F d Y).symm
          (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) := by
    intro X Y e k
    have hU := hcast' e (cast (commaCoeffR_obj F d X) k)
    have hDef : cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) e) k =
        cast (congrArg (fun Z => F.obj Z ⟶ d) e) (cast (commaCoeffR_obj F d X) k) := rfl
    have hWrap : (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) =
        cast (commaCoeffR_obj F d Y).symm
          (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) := rfl
    exact hDef.trans (hU.trans hWrap)
  rw [hbar]
  dsimp only
  refine Functor.ext (fun (j : Fin (n + 1)) => ?_) (fun j k f => ?_)
  · simp only [CategoryTheory.nerve.δ_obj]
    by_cases hle : j ≤ q.castSucc
    · have hSucc : q.castSucc.succ.succAbove j = j.castSucc :=
        Fin.succAbove_succ_of_le _ _ hle
      rw [hSucc]
      refine CostructuredArrow.obj_ext _ _ (congrArg G.obj hSucc.symm) ?_
      have eRY : G.obj ⟨n + 1, by omega⟩ =
          ((nerve C).δ q.castSucc.succ G).obj (Fin.last n) := by
        rw [CategoryTheory.nerve.δ_obj]
        exact congrArg G.obj sP.symm
      have eLY : G.obj ⟨0, by omega⟩ =
          ((nerve C).δ q.castSucc.succ G).obj (0 : Fin (n + 1)) := by
        simp [CategoryTheory.nerve.δ_obj]
      have hRw := hcastW eRY h
      have hY : (((barRightCommaEquiv F d n)
            ⟨((nerve C).δ q.castSucc.succ G),
              (cast (congrArg (unitCoeffL C).obj eLY) l,
                cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY) h)⟩).obj
            j).hom
          = F.map ((((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫
            cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY) h := rfl
      have hX : (((barRightCommaEquiv F d (n + 1)) ⟨G, l, h⟩).obj (j.castSucc)).hom
          = F.map (G.map' (j.castSucc).val (n + 1)) ≫ h := rfl
      have hH : cast (commaCoeffR_obj F d _) h = hR := rfl
      have hW : ∀ {A : C} (m : F.obj A ⟶ d),
          cast (commaCoeffR_obj F d A).symm m = m := fun m => rfl
      have hCastFull : cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY) h
          = F.map (eqToHom eRY.symm) ≫ hR :=
        hRw.trans ((hW _).trans
          (congrArg (fun m => F.map (eqToHom eRY.symm) ≫ m) hH))
      have hComb : F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫
            (F.map ((((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫
              (F.map (eqToHom eRY.symm) ≫ hR)) =
          F.map ((eqToHom (congrArg G.obj hSucc.symm) ≫
            (((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫
              eqToHom eRY.symm) ≫ hR :=
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (F.map_comp _ _).symm)).trans
          ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (F.map_comp _ _).symm))
      have eMor : ((eqToHom (congrArg G.obj hSucc.symm) ≫
            (((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫
              eqToHom eRY.symm) =
          (G.map' (j.castSucc).val (n + 1)) := by
        have hEq : eqToHom (congrArg G.obj hSucc.symm) =
            G.map (eqToHom hSucc.symm) :=
          (eqToHom_map G hSucc.symm).symm
        have hE : eRY.symm = congrArg G.obj sP := rfl
        have hEqR : eqToHom eRY.symm = G.map (eqToHom sP) :=
          (congrArg eqToHom hE).trans (eqToHom_map G sP).symm
        have hMidWsk : (((nerve C).δ q.castSucc.succ G).map' j.val n) = G.map _ := rfl
        have hRHS : (G.map' (j.castSucc).val (n + 1)) = G.map _ := rfl
        exact (congrArg (fun t => ((eqToHom (congrArg G.obj hSucc.symm) ≫ _) ≫ t))
          hEqR).trans
          ((congrArg (fun t => ((t ≫ _) ≫ G.map (eqToHom sP))) hEq).trans
          ((congrArg (fun m => ((G.map (eqToHom hSucc.symm) ≫ m) ≫
              G.map (eqToHom sP))) hMidWsk).trans
          (((congrArg (· ≫ _) (G.map_comp _ _).symm).trans
              (G.map_comp _ _).symm).trans
            ((congrArg (G.map ·) (Subsingleton.elim _ _)).trans hRHS.symm))))
      exact (congrArg (fun m => F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫ m)
        hY).trans
        ((congrArg (fun m => F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫
            (F.map ((((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫ m))
          hCastFull).trans
        (hComb.trans ((congrArg (fun m => F.map m ≫ hR) eMor).trans hX.symm)))
    · have hlt : q.castSucc < j := lt_of_not_ge hle
      have hSucc : q.castSucc.succ.succAbove j = j.succ :=
        Fin.succAbove_succ_of_lt _ _ hlt
      rw [hSucc]
      refine CostructuredArrow.obj_ext _ _ (congrArg G.obj hSucc.symm) ?_
      have eRY : G.obj ⟨n + 1, by omega⟩ =
          ((nerve C).δ q.castSucc.succ G).obj (Fin.last n) := by
        rw [CategoryTheory.nerve.δ_obj]
        exact congrArg G.obj sP.symm
      have eLY : G.obj ⟨0, by omega⟩ =
          ((nerve C).δ q.castSucc.succ G).obj (0 : Fin (n + 1)) := by
        simp [CategoryTheory.nerve.δ_obj]
      have hRw := hcastW eRY h
      have hY : (((barRightCommaEquiv F d n)
            ⟨((nerve C).δ q.castSucc.succ G),
              (cast (congrArg (unitCoeffL C).obj eLY) l,
                cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY) h)⟩).obj
            j).hom
          = F.map ((((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫
            cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY) h := rfl
      have hX : (((barRightCommaEquiv F d (n + 1)) ⟨G, l, h⟩).obj (j.succ)).hom
          = F.map (G.map' (j.succ).val (n + 1)) ≫ h := rfl
      have hH : cast (commaCoeffR_obj F d _) h = hR := rfl
      have hW : ∀ {A : C} (m : F.obj A ⟶ d),
          cast (commaCoeffR_obj F d A).symm m = m := fun m => rfl
      have hCastFull : cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY) h
          = F.map (eqToHom eRY.symm) ≫ hR :=
        hRw.trans ((hW _).trans
          (congrArg (fun m => F.map (eqToHom eRY.symm) ≫ m) hH))
      have hComb : F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫
            (F.map ((((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫
              (F.map (eqToHom eRY.symm) ≫ hR)) =
          F.map ((eqToHom (congrArg G.obj hSucc.symm) ≫
            (((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫
              eqToHom eRY.symm) ≫ hR :=
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (F.map_comp _ _).symm)).trans
          ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (F.map_comp _ _).symm))
      have eMor : ((eqToHom (congrArg G.obj hSucc.symm) ≫
            (((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫
              eqToHom eRY.symm) =
          (G.map' (j.succ).val (n + 1)) := by
        have hEq : eqToHom (congrArg G.obj hSucc.symm) =
            G.map (eqToHom hSucc.symm) :=
          (eqToHom_map G hSucc.symm).symm
        have hE : eRY.symm = congrArg G.obj sP := rfl
        have hEqR : eqToHom eRY.symm = G.map (eqToHom sP) :=
          (congrArg eqToHom hE).trans (eqToHom_map G sP).symm
        have hMidWsk : (((nerve C).δ q.castSucc.succ G).map' j.val n) = G.map _ := rfl
        have hRHS : (G.map' (j.succ).val (n + 1)) = G.map _ := rfl
        exact (congrArg (fun t => ((eqToHom (congrArg G.obj hSucc.symm) ≫ _) ≫ t))
          hEqR).trans
          ((congrArg (fun t => ((t ≫ _) ≫ G.map (eqToHom sP))) hEq).trans
          ((congrArg (fun m => ((G.map (eqToHom hSucc.symm) ≫ m) ≫
              G.map (eqToHom sP))) hMidWsk).trans
          (((congrArg (· ≫ _) (G.map_comp _ _).symm).trans
              (G.map_comp _ _).symm).trans
            ((congrArg (G.map ·) (Subsingleton.elim _ _)).trans hRHS.symm))))
      exact (congrArg (fun m => F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫ m)
        hY).trans
        ((congrArg (fun m => F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫
            (F.map ((((nerve C).δ q.castSucc.succ G).map' j.val n)) ≫ m))
          hCastFull).trans
        (hComb.trans ((congrArg (fun m => F.map m ≫ hR) eMor).trans hX.symm)))
  · apply CostructuredArrow.hom_ext _ _
    have hEq : ∀ {x y : CostructuredArrow F d} (hh : x = y),
        (eqToHom hh).left = eqToHom (congrArg CostructuredArrow.left hh) := by
      intro x y hh
      cases hh
      rfl
    rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, hEq, hEq]
    have gen : ∀ {uj uk vj vk : Fin (n + 2)} (s₁ : uj = vj) (s₂ : vk = uk)
        (e₁ : G.obj uj = G.obj vj) (e₂ : G.obj vk = G.obj uk)
        (uf : uj ⟶ uk) (vf : vj ⟶ vk),
        G.map uf = eqToHom e₁ ≫ G.map vf ≫ eqToHom e₂ := by
      intro uj uk vj vk s₁ s₂ e₁ e₂ uf vf
      have q₁ : eqToHom e₁ = G.map (eqToHom s₁) := (eqToHom_map G s₁).symm
      have q₂ : eqToHom e₂ = G.map (eqToHom s₂) := (eqToHom_map G s₂).symm
      rw [q₁, q₂, ← G.map_comp, ← G.map_comp]
      exact congrArg (G.map ·) (Subsingleton.elim _ _)
    exact gen rfl rfl _ _
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ q.castSucc.succ).op.unop).toFunctor.map f)
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ q.castSucc.succ).op.unop).toFunctor.map f)

/-- Degeneracy compatibility for the right-comma comparison. -/
theorem barRightComma_degeneracy {n : ℕ} (i : Fin (n + 1))
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D)
    (x : barObj C (commaCoeffR F d) (unitCoeffL C) n) :
    (nerve (CostructuredArrow F d)).σ i (barRightCommaEquiv F d n x) =
      barRightCommaEquiv F d (n + 1) (barσ i x) := by
  obtain ⟨G, l, h⟩ := x
  refine Functor.ext (fun j => ?_) (fun j k f => ?_)
  · refine CostructuredArrow.obj_ext _ _ rfl ?_
    change
      F.map (eqToHom rfl) ≫
        (((barRightCommaEquiv F d (n + 1))
          (barσ (R := commaCoeffR F d) (L := unitCoeffL C) i ⟨G, l, h⟩)).obj j).hom =
        (((nerve (CostructuredArrow F d)).σ i
          ((barRightCommaEquiv F d n) ⟨G, l, h⟩)).obj j).hom
    rw [eqToHom_refl, F.map_id, Category.id_comp]
    have hlen1 : (Opposite.unop (Opposite.op (SimplexCategory.mk (n + 1)))).len
        = n + 1 := by
      simp
    let hR : F.obj G.right ⟶ d := h
    have hcast' : ∀ {X Y : C} (e : X = Y) (k : F.obj X ⟶ d),
        cast (congrArg (fun Z => F.obj Z ⟶ d) e) k =
          F.map (eqToHom e.symm) ≫ k := by
      intro X Y e k
      subst e
      simp
    have hcastW : ∀ {X Y : C} (e : X = Y) (k : (commaCoeffR F d).obj (op X)),
        cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) e) k =
          cast (commaCoeffR_obj F d Y).symm
            (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) := by
      intro X Y e k
      have hU := hcast' e (cast (commaCoeffR_obj F d X) k)
      have hDef : cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) e) k =
          cast (congrArg (fun Z => F.obj Z ⟶ d) e)
            (cast (commaCoeffR_obj F d X) k) := rfl
      have hWrap : (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) =
          cast (commaCoeffR_obj F d Y).symm
            (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) := rfl
      exact hDef.trans (hU.trans hWrap)
    have eRσ : G.obj ⟨n, by omega⟩ =
        ((nerve C).σ i G).obj (Fin.last _) := by
      rw [CategoryTheory.nerve.σ_obj]
      congr 1
      exact Fin.predAbove_right_last.symm
    have eLσ : G.obj ⟨0, by omega⟩ =
        ((nerve C).σ i G).obj (0 : Fin (n + 2)) := by
      simp [CategoryTheory.nerve.σ_obj]
    have hRwσ := hcastW eRσ h
    have hYσ : (((barRightCommaEquiv F d (n + 1))
          ⟨((nerve C).σ i G),
            (cast (congrArg (unitCoeffL C).obj eLσ) l,
              cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRσ) h)⟩).obj
          j).hom
        = F.map ((((nerve C).σ i G).map' j.val (n + 1))) ≫
          cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRσ) h := rfl
    have hXσ : ((((nerve (CostructuredArrow F d)).σ i
            ((barRightCommaEquiv F d n) ⟨G, l, h⟩)).obj j).hom)
        = F.map (G.map' (i.predAbove j).val n) ≫ hR := by
      simp only [CategoryTheory.nerve.σ_obj]
      rfl
    have hH : cast (commaCoeffR_obj F d _) h = hR := rfl
    have hW : ∀ {A : C} (m : F.obj A ⟶ d),
        cast (commaCoeffR_obj F d A).symm m = m := fun m => rfl
    have hCastFullσ : cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRσ) h
        = F.map (eqToHom eRσ.symm) ≫ hR :=
      hRwσ.trans ((hW _).trans
        (congrArg (fun m => F.map (eqToHom eRσ.symm) ≫ m) hH))
    have hCombσ : F.map ((((nerve C).σ i G).map' j.val (n + 1))) ≫
          (F.map (eqToHom eRσ.symm) ≫ hR) =
        F.map (((((nerve C).σ i G).map' j.val (n + 1))) ≫
            eqToHom eRσ.symm) ≫ hR :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (F.map_comp _ _).symm)
    have eMorσ : (((((nerve C).σ i G).map' j.val (n + 1))) ≫
            eqToHom eRσ.symm) =
        (G.map' (i.predAbove j).val n) := by
      have hEσ : eRσ.symm = congrArg G.obj Fin.predAbove_right_last := rfl
      have hEqRσ : eqToHom eRσ.symm = G.map (eqToHom Fin.predAbove_right_last) :=
        (congrArg eqToHom hEσ).trans (eqToHom_map G Fin.predAbove_right_last).symm
      have hMidWskσ : ((((nerve C).σ i G).map' j.val (n + 1))) = G.map _ := rfl
      have hRHSσ : (G.map' (i.predAbove j).val n) = G.map _ := rfl
      exact (congrArg (fun t => (((((nerve C).σ i G).map' j.val (n + 1))) ≫ t))
          hEqRσ).trans
        ((congrArg (fun m => (m ≫ G.map (eqToHom Fin.predAbove_right_last)))
          hMidWskσ).trans
        ((G.map_comp _ _).symm.trans
          ((congrArg (G.map ·) (Subsingleton.elim _ _)).trans hRHSσ.symm)))
    exact hYσ.trans
      ((congrArg (fun m => F.map ((((nerve C).σ i G).map' j.val (n + 1))) ≫ m)
        hCastFullσ).trans
      (hCombσ.trans ((congrArg (fun m => F.map m ≫ hR) eMorσ).trans hXσ.symm)))
  · apply CostructuredArrow.hom_ext _ _
    have hEq : ∀ {x y : CostructuredArrow F d} (hh : x = y),
        (eqToHom hh).left = eqToHom (congrArg CostructuredArrow.left hh) := by
      intro x y hh
      cases hh
      rfl
    rw [CostructuredArrow.comp_left]
    rw [CostructuredArrow.comp_left, hEq, hEq]
    change
      ((((nerve (CostructuredArrow F d)).σ i
        ((barRightCommaEquiv F d n) ⟨G, l, h⟩)) ⋙
        CostructuredArrow.proj F d).map f) =
        𝟙 _ ≫
          ((((barRightCommaEquiv F d (n + 1))
            (barσ (R := commaCoeffR F d) (L := unitCoeffL C) i ⟨G, l, h⟩)) ⋙
            CostructuredArrow.proj F d).map f) ≫
          𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    rfl

/-- Last-face compatibility for the right-comma comparison.

The last vertex is omitted, so the comma arrow fuses via
`F.map (G.map' n (n + 1))`; the shortened chain is identified by
`Fin.succAbove_last`. -/
theorem barRightComma_face_last {n : ℕ}
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D)
    (x : barObj C (commaCoeffR F d) (unitCoeffL C) (n + 1)) :
    (nerve (CostructuredArrow F d)).δ (Fin.last (n + 1))
        (barRightCommaEquiv F d (n + 1) x) =
      barRightCommaEquiv F d n (barδ (Fin.last (n + 1)) x) := by
  obtain ⟨G, l, h⟩ := x
  have hbar :=
    barδ_last_eq (R := commaCoeffR F d) (L := unitCoeffL C) (n := n) ⟨G, l, h⟩
  rw [hbar]
  dsimp only
  refine Functor.ext (fun (j : Fin (n + 1)) => ?_) (fun j k f => ?_)
  · simp only [CategoryTheory.nerve.δ_obj]
    have hSucc : (Fin.last (n + 1)).succAbove j = j.castSucc :=
      congrFun Fin.succAbove_last j
    rw [hSucc]
    refine CostructuredArrow.obj_ext _ _ (congrArg G.obj hSucc.symm) ?_
    let hR : F.obj G.right ⟶ d := h
    have hcast' : ∀ {X Y : C} (e : X = Y) (k : F.obj X ⟶ d),
        cast (congrArg (fun Z => F.obj Z ⟶ d) e) k =
          F.map (eqToHom e.symm) ≫ k := by
      intro X Y e k
      subst e
      simp
    have hcastW : ∀ {X Y : C} (e : X = Y) (k : (commaCoeffR F d).obj (op X)),
        cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) e) k =
          cast (commaCoeffR_obj F d Y).symm
            (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) := by
      intro X Y e k
      have hU := hcast' e (cast (commaCoeffR_obj F d X) k)
      have hDef : cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) e) k =
          cast (congrArg (fun Z => F.obj Z ⟶ d) e)
            (cast (commaCoeffR_obj F d X) k) := rfl
      have hWrap : (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) =
          cast (commaCoeffR_obj F d Y).symm
            (F.map (eqToHom e.symm) ≫ cast (commaCoeffR_obj F d X) k) := rfl
      exact hDef.trans (hU.trans hWrap)
    have eLY : G.obj ⟨0, by omega⟩ =
        ((nerve C).δ (Fin.last (n + 1)) G).obj (0 : Fin (n + 1)) := by
      simp [CategoryTheory.nerve.δ_obj]
    have sP : (Fin.last (n + 1)).succAbove (Fin.last n) = ⟨n, by omega⟩ :=
      (congrFun Fin.succAbove_last (Fin.last n)).trans rfl
    have eRY : G.obj ⟨n, by omega⟩ =
        ((nerve C).δ (Fin.last (n + 1)) G).obj (Fin.last n) := by
      rw [CategoryTheory.nerve.δ_obj]
      exact congrArg G.obj sP.symm
    have hMap : (commaCoeffR F d).map (Quiver.Hom.op (G.map' n (n + 1))) h =
        F.map (G.map' n (n + 1)) ≫ hR := rfl
    have hRw := hcastW eRY
      ((commaCoeffR F d).map (Quiver.Hom.op (G.map' n (n + 1))) h)
    have hY : (((barRightCommaEquiv F d n)
          ⟨((nerve C).δ (Fin.last (n + 1)) G),
            (cast (congrArg (unitCoeffL C).obj eLY) l,
              cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY)
                ((commaCoeffR F d).map (Quiver.Hom.op (G.map' n (n + 1))) h))⟩).obj
          j).hom
        = F.map ((((nerve C).δ (Fin.last (n + 1)) G).map' j.val n)) ≫
          cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY)
            ((commaCoeffR F d).map (Quiver.Hom.op (G.map' n (n + 1))) h) := rfl
    have hX : (((barRightCommaEquiv F d (n + 1)) ⟨G, l, h⟩).obj (j.castSucc)).hom
        = F.map (G.map' (j.castSucc).val (n + 1)) ≫ hR := rfl
    have hH : cast (commaCoeffR_obj F d _)
          ((commaCoeffR F d).map (Quiver.Hom.op (G.map' n (n + 1))) h) =
        F.map (G.map' n (n + 1)) ≫ hR := rfl
    have hW : ∀ {A : C} (m : F.obj A ⟶ d),
        cast (commaCoeffR_obj F d A).symm m = m := fun m => rfl
    have hCastFull : cast (congrArg (fun Z => (commaCoeffR F d).obj (op Z)) eRY)
          ((commaCoeffR F d).map (Quiver.Hom.op (G.map' n (n + 1))) h)
        = F.map (eqToHom eRY.symm) ≫ (F.map (G.map' n (n + 1)) ≫ hR) :=
      hRw.trans ((hW _).trans
        (congrArg (fun m => F.map (eqToHom eRY.symm) ≫ m) hH))
    have hComb : F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫
          (F.map ((((nerve C).δ (Fin.last (n + 1)) G).map' j.val n)) ≫
            (F.map (eqToHom eRY.symm) ≫ (F.map (G.map' n (n + 1)) ≫ hR))) =
        F.map (((eqToHom (congrArg G.obj hSucc.symm) ≫
          (((nerve C).δ (Fin.last (n + 1)) G).map' j.val n)) ≫
            eqToHom eRY.symm) ≫ G.map' n (n + 1)) ≫ hR :=
      (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (F.map (eqToHom eRY.symm) ≫
          (F.map (G.map' n (n + 1)) ≫ hR))) (F.map_comp _ _).symm)).trans
        ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (F.map (G.map' n (n + 1)) ≫ hR))
          (F.map_comp _ _).symm))).trans
        ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ hR) (F.map_comp _ _).symm))
    have eMor : (((eqToHom (congrArg G.obj hSucc.symm) ≫
          (((nerve C).δ (Fin.last (n + 1)) G).map' j.val n)) ≫
            eqToHom eRY.symm) ≫ G.map' n (n + 1)) =
        (G.map' (j.castSucc).val (n + 1)) := by
      have hEq : eqToHom (congrArg G.obj hSucc.symm) =
          G.map (eqToHom hSucc.symm) :=
        (eqToHom_map G hSucc.symm).symm
      have hE : eRY.symm = congrArg G.obj sP := rfl
      have hEqR : eqToHom eRY.symm = G.map (eqToHom sP) :=
        (congrArg eqToHom hE).trans (eqToHom_map G sP).symm
      have hMidWsk : ((((nerve C).δ (Fin.last (n + 1)) G).map' j.val n)) =
          G.map _ := rfl
      have hC : (G.map' n (n + 1)) =
          G.map ((homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ n)) :
            (⟨n, by omega⟩ : Fin (n + 2)) ⟶ ⟨n + 1, by omega⟩)) := rfl
      have hRHS : (G.map' (j.castSucc).val (n + 1)) = G.map _ := rfl
      exact (congrArg (fun t => (((eqToHom (congrArg G.obj hSucc.symm) ≫ _) ≫ t) ≫
            G.map ((homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ n)) :
              (⟨n, by omega⟩ : Fin (n + 2)) ⟶ ⟨n + 1, by omega⟩))))
        hEqR).trans
        ((congrArg (fun t => (((eqToHom (congrArg G.obj hSucc.symm) ≫ _) ≫
            G.map (eqToHom sP)) ≫ t))
          hC).trans
        ((congrArg (fun t => (((t ≫ _) ≫ G.map (eqToHom sP)) ≫
            G.map ((homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ n)) :
              (⟨n, by omega⟩ : Fin (n + 2)) ⟶ ⟨n + 1, by omega⟩))))
          hEq).trans
        ((congrArg (fun m => (((G.map (eqToHom hSucc.symm) ≫ m) ≫
            G.map (eqToHom sP)) ≫
            G.map ((homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ n)) :
              (⟨n, by omega⟩ : Fin (n + 2)) ⟶ ⟨n + 1, by omega⟩))))
          hMidWsk).trans
        ((((congrArg (fun x => (x ≫ G.map (eqToHom sP)) ≫
            G.map ((homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ n)) :
              (⟨n, by omega⟩ : Fin (n + 2)) ⟶ ⟨n + 1, by omega⟩)))
            (G.map_comp _ _).symm).trans
          ((congrArg (· ≫ G.map ((homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ n)) :
              (⟨n, by omega⟩ : Fin (n + 2)) ⟶ ⟨n + 1, by omega⟩)))
            (G.map_comp _ _).symm).trans
            (G.map_comp _ _).symm))).trans
          ((congrArg (G.map ·) (Subsingleton.elim _ _)).trans hRHS.symm)))))
    exact (congrArg (fun m => F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫ m)
      hY).trans
      ((congrArg (fun m => F.map (eqToHom (congrArg G.obj hSucc.symm)) ≫
          (F.map ((((nerve C).δ (Fin.last (n + 1)) G).map' j.val n)) ≫ m))
        hCastFull).trans
      (hComb.trans ((congrArg (fun m => F.map m ≫ hR) eMor).trans hX.symm)))
  · apply CostructuredArrow.hom_ext _ _
    have hEq : ∀ {x y : CostructuredArrow F d} (hh : x = y),
        (eqToHom hh).left = eqToHom (congrArg CostructuredArrow.left hh) := by
      intro x y hh
      cases hh
      rfl
    rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, hEq, hEq]
    have gen : ∀ {uj uk vj vk : Fin (n + 2)} (s₁ : uj = vj) (s₂ : vk = uk)
        (e₁ : G.obj uj = G.obj vj) (e₂ : G.obj vk = G.obj uk)
        (uf : uj ⟶ uk) (vf : vj ⟶ vk),
        G.map uf = eqToHom e₁ ≫ G.map vf ≫ eqToHom e₂ := by
      intro uj uk vj vk s₁ s₂ e₁ e₂ uf vf
      have q₁ : eqToHom e₁ = G.map (eqToHom s₁) := (eqToHom_map G s₁).symm
      have q₂ : eqToHom e₂ = G.map (eqToHom s₂) := (eqToHom_map G s₂).symm
      rw [q₁, q₂, ← G.map_comp, ← G.map_comp]
      exact congrArg (G.map ·) (Subsingleton.elim _ _)
    exact gen rfl rfl _ _
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ (Fin.last (n + 1))).op.unop).toFunctor.map f)
      ((SimplexCategory.toCat.map
        (SimplexCategory.δ (Fin.last (n + 1))).op.unop).toFunctor.map f)

/-- Full face compatibility for the right-comma `Data` isomorphism.

Dispatches an arbitrary `i : Fin (n + 2)` by `i.val = 0`, `i.val = n + 1`,
and the interior `q := ⟨i.val - 1, by omega⟩`. -/
theorem barRightComma_face_compat {n : ℕ} (i : Fin (n + 2))
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    (Equiv.toIso (barRightCommaEquiv F d (n + 1))).hom ≫
        (nerveData (CostructuredArrow F d)).δ i =
      (categoryBarData (R := commaCoeffR F d) (L := unitCoeffL C)).δ i ≫
        (Equiv.toIso (barRightCommaEquiv F d n)).hom := by
  ext x
  change (nerve (CostructuredArrow F d)).δ i (barRightCommaEquiv F d (n + 1) x) =
    barRightCommaEquiv F d n (barδ i x)
  by_cases h0 : i.val = 0
  · have hi0 : i = 0 := Fin.ext h0
    subst hi0
    exact barRightComma_face_zero F d x
  · by_cases hL : i.val = n + 1
    · have hiL : i = Fin.last (n + 1) := by
        apply Fin.ext
        rw [hL]
        simp [Fin.val_last]
      subst hiL
      exact barRightComma_face_last F d x
    · obtain ⟨q, hk⟩ : ∃ q : Fin n, i.val = q.val + 1 :=
        ⟨⟨i.val - 1, by omega⟩, by change i.val = i.val - 1 + 1; omega⟩
      have hi : i = q.castSucc.succ := by
        apply Fin.ext
        simp [Fin.val_succ, Fin.val_castSucc, hk]
      subst hi
      exact barRightComma_face_interior q F d x

/-- Full degeneracy compatibility for the right-comma `Data` isomorphism, by function
extensionality and the pointwise lemma. -/
theorem barRightComma_degeneracy_compat {n : ℕ} (i : Fin (n + 1))
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    (Equiv.toIso (barRightCommaEquiv F d n)).hom ≫
        (nerveData (CostructuredArrow F d)).σ i =
      (categoryBarData (R := commaCoeffR F d) (L := unitCoeffL C)).σ i ≫
        (Equiv.toIso (barRightCommaEquiv F d (n + 1))).hom := by
  ext x
  change (nerve (CostructuredArrow F d)).σ i (barRightCommaEquiv F d n x) =
    barRightCommaEquiv F d (n + 1) (barσ i x)
  exact barRightComma_degeneracy i F d x

/-- Simplicial `Data` isomorphism between the right-comma bar and the comma-category nerve,
assembled from the degreewise equivalence with `Data.isoOfIso`. -/
noncomputable def barRightCommaDataIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    categoryBarData (R := commaCoeffR F d) (L := unitCoeffL C) ≅
      nerveData (CostructuredArrow F d) :=
  SimplicialObject.Data.isoOfIso (fun n => Equiv.toIso (barRightCommaEquiv F d n))
    (fun i => barRightComma_face_compat i F d)
    (fun i => barRightComma_degeneracy_compat i F d)

/-- Simplicial-set isomorphism between the right-comma bar and the comma-category nerve.

Composes the promoted data iso with the nerve-data comparison. -/
noncomputable def barRightCommaSimplicialIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    categoryBar (R := commaCoeffR F d) (L := unitCoeffL C) ≅
      nerve (CostructuredArrow F d) :=
  (SimplicialObject.Data.toSimplicialFunctor.mapIso
    (barRightCommaDataIso F d)).trans (nerveDataSimplicialIso _)

end CategoryBar

end CategoryTheory
