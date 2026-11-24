/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.Quasicategory.TerminalVertexCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.WithTerminal.Cone
import MathlibExt.CategoryTheory.NerveCrossUniverse

/-!
# Terminal vertices of the ordinary nerve

For a category `C` with independent object and morphism universes and an
object `c`, the native join over-slice at `c` is the nerve of `Over c`.
Its original projection is `nerveMapCross (Over.forget c)`, with
compatibility for every simplex operator. Both nerves live in the maximum
of the object and morphism universes.

The native all-boundary lifting condition recognizes exactly terminality
of the original object `c`. A terminal object makes the original
projection an isomorphism, supplying lifts in every dimension. Conversely,
boundary zero gives an arrow from every object to `c`, and boundary one
over an identity arrow makes any two such arrows equal.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe uObj uHom

namespace SSet

variable {C : Type uObj} [Category.{uHom} C] {c : C} {n : ℕ}

/-!
## Chains ending at the given object
-/

local instance (n : ℕ) : Quiver.IsThin (WithTerminal (Fin (n + 1))) := fun a b => by
  cases a <;> cases b <;>
    change Subsingleton (WithTerminal.Hom _ _) <;>
    dsimp only [WithTerminal.Hom] <;> infer_instance

private def finWithTerminal (n : ℕ) : Fin (n + 2) ⥤ WithTerminal (Fin (n + 1)) where
  obj i := Fin.lastCases WithTerminal.star WithTerminal.of i
  map {i j} f := by
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last =>
        simpa only [Fin.lastCases_last] using
          (𝟙 (WithTerminal.star : WithTerminal (Fin (n + 1))))
      | cast j => exact False.elim (by simpa using leOfHom f)
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        simpa only [Fin.lastCases_castSucc, Fin.lastCases_last, WithTerminal.incl] using
          WithTerminal.homFrom i
      | cast j =>
        simpa only [Fin.lastCases_castSucc, WithTerminal.incl] using
          WithTerminal.incl.map (homOfLE (show i ≤ j from by simpa using leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def extendOver (F : ComposableArrows (Over c) n) : ComposableArrows C (n + 1) :=
  finWithTerminal n ⋙ WithTerminal.liftFromOver.obj F

private lemma obj_cast (F : ComposableArrows (Over c) n) (i : Fin (n + 1)) :
    (extendOver F).obj i.castSucc = (F.obj i).left := by
  simp [extendOver, finWithTerminal]

private lemma obj_last (F : ComposableArrows (Over c) n) :
    (extendOver F).obj (Fin.last (n + 1)) = c := by
  simp [extendOver, finWithTerminal]

private lemma incl_finWithTerminal (n : ℕ) :
    Fin.castSuccFunctor (n + 1) ⋙ finWithTerminal n = WithTerminal.incl := by
  refine CategoryTheory.Functor.ext (fun i => ?_) (fun i j f => ?_)
  · simp [finWithTerminal, WithTerminal.incl]
  · apply Subsingleton.elim

private lemma extendOver_restriction (F : ComposableArrows (Over c) n) :
    (extendOver F).δlast = F ⋙ Over.forget c := by
  change Fin.castSuccFunctor _ ⋙ (finWithTerminal n ⋙ _) = _
  rw [← CategoryTheory.Functor.assoc, incl_finWithTerminal]
  rfl

private lemma extendOver_map_cast (F : ComposableArrows (Over c) n)
    {i j : Fin (n + 1)} (h : i ⟶ j) :
    (extendOver F).map ((Fin.castSuccFunctor _).map h) =
      eqToHom (obj_cast F i) ≫ (F.map h).left ≫ eqToHom (obj_cast F j).symm := by
  exact CategoryTheory.Functor.congr_hom (extendOver_restriction F) h

private lemma finWithTerminal_obj_cast (n : ℕ) (i : Fin (n + 1)) :
    (finWithTerminal n).obj i.castSucc = WithTerminal.of i := by
  simp [finWithTerminal]

private lemma finWithTerminal_obj_last (n : ℕ) :
    (finWithTerminal n).obj (Fin.last (n + 1)) = WithTerminal.star := by
  simp [finWithTerminal]

private lemma finWithTerminal_to_last (n : ℕ) (i : Fin (n + 1)) :
    (finWithTerminal n).map (homOfLE (Fin.le_last i.castSucc)) =
      eqToHom (finWithTerminal_obj_cast n i) ≫ WithTerminal.homFrom i ≫
        eqToHom (finWithTerminal_obj_last n).symm :=
  Subsingleton.elim _ _

private lemma extendOver_map_last (F : ComposableArrows (Over c) n) (i : Fin (n + 1)) :
    (extendOver F).map (homOfLE (Fin.le_last i.castSucc)) =
      eqToHom (obj_cast F i) ≫ (F.obj i).hom ≫ eqToHom (obj_last F).symm := by
  change (WithTerminal.liftFromOver.obj F).map ((finWithTerminal n).map _) = _
  rw [finWithTerminal_to_last]
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.eqToHom_map]
  rfl

private lemma over_eq_of_left {A B : Over c} (h : A.left = B.left)
    (w : A.hom = eqToHom h ≫ B.hom) : A = B := by
  cases A with | mk a ra fa =>
    cases B with | mk b rb fb =>
      cases ra
      cases rb
      change a = b at h
      change fa = eqToHom h ≫ fb at w
      subst b
      simp only [eqToHom_refl, Category.id_comp] at w
      subst fb
      rfl

private def lastCone (G : ComposableArrows C (n + 1))
    (h : G.obj (Fin.last (n + 1)) = c) :
    G.δlast ⟶ (CategoryTheory.Functor.const _).obj c where
  app i := G.map (homOfLE (Fin.le_last i.castSucc)) ≫ eqToHom h
  naturality i j f := by
    change G.map ((Fin.castSuccFunctor _).map f) ≫
        (G.map (homOfLE (Fin.le_last j.castSucc)) ≫ eqToHom h) =
      (G.map (homOfLE (Fin.le_last i.castSucc)) ≫ eqToHom h) ≫ 𝟙 c
    rw [Category.comp_id, ← Category.assoc, ← G.map_comp]
    rfl

private def truncateOver (G : ComposableArrows C (n + 1))
    (h : G.obj (Fin.last (n + 1)) = c) : ComposableArrows (Over c) n :=
  Over.lift G.δlast (lastCone G h)

private lemma truncateOver_extendOver (F : ComposableArrows (Over c) n) :
    truncateOver (extendOver F) (obj_last F) = F := by
  have h_obj : ∀ i, (truncateOver (extendOver F) (obj_last F)).obj i = F.obj i := by
    intro i
    apply over_eq_of_left (obj_cast F i)
    change (extendOver F).map (homOfLE _) ≫ eqToHom _ = _
    rw [extendOver_map_last]
    simp
  refine CategoryTheory.Functor.ext h_obj (fun i j f => ?_)
  apply Over.OverMorphism.ext
  simp only [Over.eqToHom_left, Over.comp_left]
  exact CategoryTheory.Functor.congr_hom (extendOver_restriction F) f

private lemma extendOver_truncateOver (G : ComposableArrows C (n + 1))
    (h : G.obj (Fin.last (n + 1)) = c) :
    extendOver (truncateOver G h) = G := by
  have h_obj : ∀ i, (extendOver (truncateOver G h)).obj i = G.obj i := by
    intro i
    cases i using Fin.lastCases with
    | last => exact (obj_last _).trans h.symm
    | cast i => exact obj_cast _ i
  refine CategoryTheory.Functor.ext h_obj (fun i j f => ?_)
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last =>
      have hf : f = 𝟙 _ := Subsingleton.elim _ _
      simp [hf]
    | cast j => exact False.elim (by simpa using leOfHom f)
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      rw [show f = homOfLE (Fin.le_last i.castSucc) from Subsingleton.elim _ _]
      rw [extendOver_map_last]
      change (eqToHom (obj_cast (truncateOver G h) i) ≫
          (G.map (homOfLE (Fin.le_last i.castSucc)) ≫ eqToHom h) ≫
          eqToHom (obj_last (truncateOver G h)).symm) =
        eqToHom (obj_cast (truncateOver G h) i) ≫ G.map (homOfLE (Fin.le_last i.castSucc)) ≫
          eqToHom ((obj_last (truncateOver G h)).trans h.symm).symm
      simp only [Category.assoc, eqToHom_trans]
    | cast j =>
      exact extendOver_map_cast (truncateOver G h) (homOfLE (show i ≤ j from by
        simpa using leOfHom f))

/- The two ordinal calculations below are the same scalar computations
used privately in `JoinSliceRightPointedOrdinal`. They are kept local to
this comparison, which uses the existing public join naturality API. -/
private lemma tensorWithPoint_cast {m k : ℕ} (f : ⦋m⦌ ⟶ ⦋k⦌) (i : Fin (m + 1)) :
    (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom i.castSucc =
      (f.toOrderHom i).castSucc := by
  change Fin.addCases (motive := fun _ => Fin (k + 2))
    (fun j => Fin.castAdd 1 (f.toOrderHom j))
    (fun j : Fin 1 => Fin.natAdd (k + 1) j) (Fin.castAdd 1 i) = (f.toOrderHom i).castSucc
  rw [Fin.addCases_left]
  rfl

private lemma tensorWithPoint_last {m k : ℕ} (f : ⦋m⦌ ⟶ ⦋k⦌) :
    (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom (Fin.last (m + 1)) =
      Fin.last (k + 1) := by
  change Fin.addCases (motive := fun _ => Fin (k + 2))
    (fun j => Fin.castAdd 1 (f.toOrderHom j))
    (fun j : Fin 1 => Fin.natAdd (k + 1) j) (Fin.natAdd (m + 1) (0 : Fin 1)) =
    Fin.last (k + 1)
  rw [Fin.addCases_right]
  rfl

private lemma finWithTerminal_operator {m k : ℕ} (f : ⦋m⦌ ⟶ ⦋k⦌) :
    finWithTerminal m ⋙ WithTerminal.map f.toOrderHom.monotone.functor =
      (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom.monotone.functor ⋙
        finWithTerminal k := by
  refine CategoryTheory.Functor.ext (fun i => ?_) (fun i j g => Subsingleton.elim _ _)
  cases i using Fin.lastCases with
  | last =>
    simp only [CategoryTheory.Functor.comp_obj, finWithTerminal, Fin.lastCases_last,
      WithTerminal.map_obj]
    change WithTerminal.star = Fin.lastCases WithTerminal.star WithTerminal.of
      ((AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom (Fin.last (m + 1)))
    rw [tensorWithPoint_last]
    exact (finWithTerminal_obj_last k).symm
  | cast i =>
    simp only [CategoryTheory.Functor.comp_obj, finWithTerminal, Fin.lastCases_castSucc,
      WithTerminal.map_obj]
    change WithTerminal.of (f.toOrderHom i) = Fin.lastCases WithTerminal.star WithTerminal.of
      ((AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom i.castSucc)
    rw [tensorWithPoint_cast]
    exact (finWithTerminal_obj_cast k (f.toOrderHom i)).symm

private lemma liftFromOver_operator {m k : ℕ} (f : ⦋m⦌ ⟶ ⦋k⦌)
    (F : ComposableArrows (Over c) k) :
    WithTerminal.map f.toOrderHom.monotone.functor ⋙ WithTerminal.liftFromOver.obj F =
      WithTerminal.liftFromOver.obj (f.toOrderHom.monotone.functor ⋙ F) := by
  refine CategoryTheory.Functor.ext (fun i => ?_) (fun i j g => ?_)
  · cases i <;> rfl
  · cases i <;> cases j
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    · exact WithTerminal.false_of_from_star g |>.elim
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl

private lemma extendOver_operator {m k : ℕ} (f : ⦋m⦌ ⟶ ⦋k⦌)
    (F : ComposableArrows (Over c) k) :
    extendOver (f.toOrderHom.monotone.functor ⋙ F) =
      (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom.monotone.functor ⋙
        extendOver F := by
  unfold extendOver
  rw [← liftFromOver_operator, ← CategoryTheory.Functor.assoc, finWithTerminal_operator,
    CategoryTheory.Functor.assoc]
  rfl

/-!
## The native comparison and its original projection
-/

private def chainOverEquiv (n : ℕ) :
    {G : ComposableArrows C (n + 1) // G.obj (Fin.last (n + 1)) = c} ≃
      ComposableArrows (Over c) n where
  toFun G := truncateOver G.1 G.2
  invFun F := ⟨extendOver F, obj_last F⟩
  left_inv G := Subtype.ext (extendOver_truncateOver G.1 G.2)
  right_inv F := truncateOver_extendOver F

private abbrev point (c : C) : (Δ[0] : SSet.{max uObj uHom}) ⟶ nerve C :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₀ c)

private lemma last_condition (g : (Δ[n + 1] : SSet.{max uObj uHom}) ⟶ nerve C) :
    rightVertex n ≫ g = point c ↔
      (SSet.yonedaEquiv g).obj (Fin.last (n + 1)) = c := by
  constructor
  · intro h
    have h' := congrArg SSet.yonedaEquiv h
    rw [rightVertex_eq, ← yonedaEquiv_naturality] at h'
    have h'' := CategoryTheory.Functor.congr_obj h' (0 : Fin 1)
    change (SSet.yonedaEquiv g).obj ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom 0) =
      (SSet.yonedaEquiv (point c)).obj 0 at h''
    rw [SSet.inr'_toOrderHom_zero] at h''
    simpa only [point, Equiv.apply_symm_apply, ComposableArrows.mk₀_obj] using h''
  · intro h
    apply SSet.yonedaEquiv.injective
    rw [rightVertex_eq, ← yonedaEquiv_naturality]
    apply ComposableArrows.ext₀
    change (SSet.yonedaEquiv g).obj ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom 0) =
      (SSet.yonedaEquiv (point c)).obj 0
    rw [SSet.inr'_toOrderHom_zero]
    simpa only [point, Equiv.apply_symm_apply, ComposableArrows.mk₀_obj] using h

private def nativeOverEquiv (n : ℕ) :
    (sliceOver (nerve C) (point c)).obj (op ⦋n⦌) ≃ ComposableArrows (Over c) n :=
  (sliceOver.simplexEquivSucc (nerve C) (point c) n).trans
    ((Equiv.subtypeEquiv SSet.yonedaEquiv (fun g => last_condition g)).trans (chainOverEquiv n))

private lemma nativeOverEquiv_symm_val (F : ComposableArrows (Over c) n) :
    ((nativeOverEquiv n).symm F).val =
      (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm (extendOver F) := rfl

private lemma nativeOverEquiv_symm_operator {m k : ℕ} (f : ⦋m⦌ ⟶ ⦋k⦌)
    (F : ComposableArrows (Over c) k) :
    (nativeOverEquiv m).symm ((nerve (Over c)).map f.op F) =
      (sliceOver (nerve C) (point c)).map f.op ((nativeOverEquiv k).symm F) := by
  let x : (nerve C) _⦋k + 1⦌ := extendOver F
  let x' : (nerve C) _⦋m + 1⦌ := extendOver (f.toOrderHom.monotone.functor ⋙ F)
  have hx : x' = (nerve C).map (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋0⦌)).op x :=
    extendOver_operator f F
  apply Subtype.ext
  simp only [nativeOverEquiv_symm_val, sliceOver.map_val]
  change (joinStdSimplexIso m 0).hom ≫ SSet.yonedaEquiv.symm x' =
    (join.map (stdSimplex.map f)).app Δ[0] ≫
      ((joinStdSimplexIso k 0).hom ≫ SSet.yonedaEquiv.symm x)
  let P := stdSimplex.map (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋0⦌))
  have hP : P ≫ SSet.yonedaEquiv.symm x = SSet.yonedaEquiv.symm x' :=
    (SSet.yonedaEquiv_symm_naturality_left _ x).trans (congrArg SSet.yonedaEquiv.symm hx).symm
  calc
    _ = (joinStdSimplexIso m 0).hom ≫ (P ≫ SSet.yonedaEquiv.symm x) :=
      congrArg (fun q => (joinStdSimplexIso m 0).hom ≫ q) hP.symm
    _ = ((joinStdSimplexIso m 0).hom ≫ P) ≫ SSet.yonedaEquiv.symm x :=
      (Category.assoc _ _ _).symm
    _ = ((join.map (stdSimplex.map f)).app Δ[0] ≫ (joinStdSimplexIso k 0).hom) ≫
        SSet.yonedaEquiv.symm x :=
      congrArg (fun q => q ≫ SSet.yonedaEquiv.symm x) (joinStdSimplexIso_natural_left f).symm
    _ = _ := Category.assoc _ _ _

private def nativeNerveIso : sliceOver (nerve C) (point c) ≅ nerve (Over c) :=
  NatIso.ofComponents (fun d => (nativeOverEquiv d.unop.len).toIso) (by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro g
    change (nativeOverEquiv m) ((sliceOver (nerve C) (point c)).map α g) =
      (nerve (Over c)).map α ((nativeOverEquiv n) g)
    apply (nativeOverEquiv m).symm.injective
    simp only [Equiv.symm_apply_apply]
    exact (congrArg (fun z => (sliceOver (nerve C) (point c)).map α z)
      ((nativeOverEquiv n).symm_apply_apply g)).symm.trans
        (nativeOverEquiv_symm_operator α.unop ((nativeOverEquiv n) g)).symm)

private lemma nativeNerveIso_inv_projection :
    nativeNerveIso.inv ≫ sliceOver.proj (nerve C) (point c) = nerveMapCross (Over.forget c) := by
  ext ⟨⟨n⟩⟩ F
  let x : (nerve C) _⦋n + 1⦌ := extendOver F
  change SSet.yonedaEquiv (joinInl Δ[n] Δ[0] ≫
      ((joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm x)) =
    (nerveMapCross (Over.forget c)).app _ F
  rw [← Category.assoc, joinInl_comp_joinStdSimplexIso_hom,
    ← SSet.yonedaEquiv_naturality]
  have hF : (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌).toOrderHom.monotone.functor =
      Fin.castSuccFunctor (n + 1) := by
    refine CategoryTheory.Functor.ext (fun i => ?_) (fun i j f => Subsingleton.elim _ _)
    change (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌).toOrderHom i = i.castSucc
    rw [AugmentedSimplexCategory.inl'_eval]
    rfl
  change (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌).toOrderHom.monotone.functor ⋙
      extendOver F = F ⋙ Over.forget c
  rw [hF]
  exact extendOver_restriction F

private lemma nativeNerveIso_hom_projection :
    nativeNerveIso.hom ≫ nerveMapCross (Over.forget c) = sliceOver.proj (nerve C) (point c) := by
  rw [← cancel_epi nativeNerveIso.inv, Iso.inv_hom_id_assoc, nativeNerveIso_inv_projection]

/-!
## Terminality and boundary lifting
-/

private def terminalOverFunctor (hc : IsTerminal c) : C ⥤ Over c :=
  (Over.equivalenceOfIsTerminal hc).inverse

private lemma forget_terminalOverFunctor (hc : IsTerminal c) :
    Over.forget c ⋙ terminalOverFunctor hc = 𝟭 (Over c) := by
  have h_obj : ∀ A : Over c, (Over.forget c ⋙ terminalOverFunctor hc).obj A = A := by
    intro A
    refine over_eq_of_left (A := (Over.forget c ⋙ terminalOverFunctor hc).obj A)
      (B := A) (by rfl) ?_
    simp only [eqToHom_refl, Category.id_comp]
    exact hc.hom_ext _ _
  refine CategoryTheory.Functor.ext h_obj (fun A B f => ?_)
  apply Over.OverMorphism.ext
  simp only [Over.eqToHom_left, Over.comp_left]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private def terminalNerveIso (hc : IsTerminal c) : nerve (Over c) ≅ nerve C where
  hom := nerveMapCross (Over.forget c)
  inv := { app _ := ↾fun F => ((terminalOverFunctor hc).mapComposableArrows _).obj F }
  hom_inv_id := by
    ext d F
    change (F ⋙ Over.forget c) ⋙ terminalOverFunctor hc = F
    rw [CategoryTheory.Functor.assoc, forget_terminalOverFunctor,
      CategoryTheory.Functor.comp_id]
  inv_hom_id := by
    ext d F
    rfl

private lemma native_terminal_of_terminal (hc : IsTerminal c) : IsTerminalVertex (point c) := by
  have hq : IsIso (nerveMapCross (Over.forget c)) := by
    change IsIso (terminalNerveIso hc).hom
    infer_instance
  have hp : IsIso (sliceOver.proj (nerve C) (point c)) := by
    rw [← nativeNerveIso_hom_projection]
    infer_instance
  apply (isTerminalVertex_iff _).mpr
  intro m
  infer_instance

private lemma hom_nonempty_of_boundary_zero
    (h : HasLiftingProperty (boundary.{max uObj uHom} 0).ι (nerveMapCross (Over.forget c)))
    (x : C) : Nonempty (x ⟶ c) := by
  let a : (∂Δ[0] : SSet.{max uObj uHom}) ⟶ nerve (Over c) :=
    (boundary 0).ι ≫ SSet.yonedaEquiv.symm (ComposableArrows.mk₀ (Over.mk (𝟙 c)))
  have sq : CommSq a (boundary 0).ι (nerveMapCross (Over.forget c)) (point x) :=
    ⟨boundary.hom_ext₀⟩
  have h' := congrArg SSet.yonedaEquiv sq.fac_right
  simp only [SSet.yonedaEquiv_comp, point, Equiv.apply_symm_apply] at h'
  let A : Over c := nerveEquiv (SSet.yonedaEquiv sq.lift)
  have hA : A.left = x := CategoryTheory.Functor.congr_obj h' (0 : Fin 1)
  exact ⟨eqToHom hA.symm ≫ A.hom⟩

private lemma hom_eq_of_boundary_one
    (h : HasLiftingProperty (boundary.{max uObj uHom} 1).ι (nerveMapCross (Over.forget c)))
    {x : C} (f g : x ⟶ c) : f = g := by
  let x₀ : (nerve (Over c)) _⦋0⦌ := ComposableArrows.mk₀ (Over.mk f)
  let x₁ : (nerve (Over c)) _⦋0⦌ := ComposableArrows.mk₀ (Over.mk g)
  let a := boundaryOneMap x₀ x₁
  let b : (Δ[1] : SSet.{max uObj uHom}) ⟶ nerve C :=
    SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (𝟙 x))
  have ha₀ : boundary.ι (0 : Fin 2) ≫ a = SSet.const x₁ :=
    boundary_ι_zero_boundaryOneMap x₀ x₁
  have ha₁ : boundary.ι (1 : Fin 2) ≫ a = SSet.const x₀ :=
    boundary_ι_one_boundaryOneMap x₀ x₁
  have hq₀ : (nerveMapCross (Over.forget c)).app (op ⦋0⦌) x₀ = ComposableArrows.mk₀ x :=
    nerveMapCross_app_mk₀ (Over.forget c) (Over.mk f)
  have hq₁ : (nerveMapCross (Over.forget c)).app (op ⦋0⦌) x₁ = ComposableArrows.mk₀ x :=
    nerveMapCross_app_mk₀ (Over.forget c) (Over.mk g)
  have sq : CommSq a (boundary 1).ι (nerveMapCross (Over.forget c)) b := by
    constructor
    apply boundary.hom_ext
    intro i
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    obtain rfl | rfl : i = (0 : Fin 2) ∨ i = 1 :=
      hi.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    all_goals
      simp only [← Category.assoc, boundary.ι_ι]
      first | rw [ha₀] | rw [ha₁]
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp]
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const]
      first | rw [hq₀] | rw [hq₁]
      simp only [b, Equiv.apply_symm_apply]
      apply ComposableArrows.ext₀
      rfl
  let σ : (nerve (Over c)) _⦋1⦌ := SSet.yonedaEquiv sq.lift
  have hs : (nerve (Over c)).δ 1 σ = x₀ := by
    have hi := congrArg (fun q => boundary.ι (1 : Fin 2) ≫ q) sq.fac_left
    have hi' := congrArg SSet.yonedaEquiv hi
    simpa only [← Category.assoc, boundary.ι_ι, a,
      boundary_ι_one_boundaryOneMap, SSet.yonedaEquiv_const,
      stdSimplex.yonedaEquiv_δ_comp] using hi'
  have ht : (nerve (Over c)).δ 0 σ = x₁ := by
    have hi := congrArg (fun q => boundary.ι (0 : Fin 2) ≫ q) sq.fac_left
    have hi' := congrArg SSet.yonedaEquiv hi
    simpa only [← Category.assoc, boundary.ι_ι, a,
      boundary_ι_zero_boundaryOneMap, SSet.yonedaEquiv_const,
      stdSimplex.yonedaEquiv_δ_comp] using hi'
  let e : (nerve (Over c)).Edge x₀ x₁ := Edge.mk σ hs ht
  obtain ⟨γ, hγ⟩ := nerve.edgeMk_surjective e
  have hb : (e.map (nerveMapCross (Over.forget c))).edge = ComposableArrows.mk₁ (𝟙 x) := by
    have hb' := congrArg SSet.yonedaEquiv sq.fac_right
    change (nerveMapCross (Over.forget c)).app (op ⦋1⦌) (SSet.yonedaEquiv sq.lift) = _
    simpa only [SSet.yonedaEquiv_comp, b, Equiv.apply_symm_apply] using hb'
  have hγmap : (nerveMapCross (Over.forget c)).app (op ⦋1⦌)
      (ComposableArrows.mk₁ γ) = ComposableArrows.mk₁ (𝟙 x) :=
    (congrArg (fun ε => (ε.map (nerveMapCross (Over.forget c))).edge) hγ).trans hb
  have hγleft : γ.left = 𝟙 x := by
    rw [nerveMapCross_app_mk₁] at hγmap
    exact Arrow.mk_injective x x
      (congrArg (fun F : ComposableArrows C 1 => Arrow.mk F.hom) hγmap)
  have hw := Over.w γ
  change γ.left ≫ g = f at hw
  calc
    f = γ.left ≫ g := hw.symm
    _ = (𝟙 x) ≫ g := congrArg (fun k => k ≫ g) hγleft
    _ = g := Category.id_comp g

private def terminal_of_native_terminal (h : IsTerminalVertex (point c)) : IsTerminal c := by
  have hq : ∀ m : ℕ,
      HasLiftingProperty (boundary.{max uObj uHom} m).ι (nerveMapCross (Over.forget c)) := by
    intro m
    have hm := (isTerminalVertex_iff _).mp h m
    rw [← nativeNerveIso_inv_projection (c := c)]
    infer_instance
  let arrows : ∀ x : C, x ⟶ c :=
    fun x => Classical.choice (hom_nonempty_of_boundary_zero (hq 0) x)
  exact IsTerminal.ofUniqueHom arrows (fun x f => hom_eq_of_boundary_one (hq 1) f (arrows x))

/-!
## Public ordinary-nerve bridge
-/

/-- The native join over-slice at the actual vertex of `c` is the
ordinary nerve of the category of arrows into `c`. -/
def sliceOverNerveIso (C : Type uObj) [Category.{uHom} C] (c : C) :
    sliceOver (nerve C) (yonedaEquiv.symm (ComposableArrows.mk₀ c)) ≅ nerve (Over c) :=
  nativeNerveIso

/-- The comparison retains the original projection to the nerve of `C`. -/
@[reassoc (attr := simp)]
theorem sliceOverNerveIso_hom_nerveMap_forget (c : C) :
    (sliceOverNerveIso C c).hom ≫ nerveMapCross (Over.forget c) =
      sliceOver.proj (nerve C) (yonedaEquiv.symm (ComposableArrows.mk₀ c)) :=
  nativeNerveIso_hom_projection

/-- The inverse comparison reads the original projection as the
nerve of the ordinary forgetful functor. -/
@[reassoc (attr := simp)]
theorem sliceOverNerveIso_inv_proj (c : C) :
    (sliceOverNerveIso C c).inv ≫
        sliceOver.proj (nerve C) (yonedaEquiv.symm (ComposableArrows.mk₀ c)) =
      nerveMapCross (Over.forget c) :=
  nativeNerveIso_inv_projection

/-- Ordinary terminality supplies the original native lifts of every
standard boundary, including dimension zero. -/
theorem isTerminalVertex_nerve_of_isTerminal (hc : IsTerminal c) :
    IsTerminalVertex ((yonedaEquiv (X := nerve C)).symm (ComposableArrows.mk₀ c)) :=
  native_terminal_of_terminal hc

/-- The actual vertex of an ordinary nerve is terminal precisely when
its given original object is terminal in the ordinary category. -/
theorem isTerminalVertex_nerve_iff (c : C) :
    IsTerminalVertex ((yonedaEquiv (X := nerve C)).symm (ComposableArrows.mk₀ c)) ↔
      Nonempty (CategoryTheory.Limits.IsTerminal c) :=
  ⟨fun h => ⟨terminal_of_native_terminal h⟩, fun ⟨hc⟩ => native_terminal_of_terminal hc⟩

end SSet
