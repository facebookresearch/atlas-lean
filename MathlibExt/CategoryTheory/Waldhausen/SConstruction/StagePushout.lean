/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibration
public import MathlibExt.CategoryTheory.Waldhausen.Exact
import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutCokernel
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutCofibrationSequence

/-!
# Pointwise pushouts of finite stages

A `StagePushoutPresentation` records a functorial family of component
pushouts of two stage maps with a common source.  If the first map is a
genuine `stageCofibrations` morphism, the apex diagram is again an `IsStage`.

The proof uses the successor pushout data in the definition of
`stageCofibrations`, not pointwise cofibrations.  It first proves successor
zero-row cofibrations by two cobase changes, obtains all zero-row cofiber
triples from the existing levelwise-pushout cokernel theorem, and then uses
pushout cancellation to obtain every shifted cofiber triple.

There is no Waldhausen instance on stages, all-row propagation theorem,
rho construction, weak-equivalence, realization, or additivity claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance stagePushoutWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- A functorial pointwise pushout of two stage maps with a common source.
No stage property is assumed for the apex. -/
structure StagePushoutPresentation {n : ℕ} {A M N : Stage C n}
    (f : A ⟶ M) (g : A ⟶ N) where
  /-- The candidate pushout diagram. -/
  apex : Ar n ⥤ C
  /-- The first cocone leg. -/
  inl : M.obj ⟶ apex
  /-- The second cocone leg. -/
  inr : N.obj ⟶ apex
  /-- Every component square is a pushout. -/
  isPushout_app : ∀ x : Ar n,
    IsPushout (f.hom.app x) (g.hom.app x) (inl.app x) (inr.app x)

namespace StagePushoutPresentation

variable {C}
variable {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}

/-- The apex map is the map induced by the component pushouts. -/
theorem map_eq_desc (P : StagePushoutPresentation C f g)
    {x y : Ar n} (r : x ⟶ y) :
    P.apex.map r =
      (P.isPushout_app x).desc
        (M.obj.map r ≫ P.inl.app y)
        (N.obj.map r ≫ P.inr.app y) (by
          rw [← Category.assoc, ← f.hom.naturality r,
            Category.assoc, (P.isPushout_app y).w, ← Category.assoc,
            g.hom.naturality r, Category.assoc]) := by
  apply (P.isPushout_app x).hom_ext
  · rw [(P.isPushout_app x).inl_desc]
    exact (P.inl.naturality r).symm
  · rw [(P.isPushout_app x).inr_desc]
    exact (P.inr.naturality r).symm

/-- Diagonal values of the apex are zero objects. -/
private theorem apex_diag_isZero (P : StagePushoutPresentation C f g)
    (i : Fin (n + 1)) : IsZero (P.apex.obj (diag i)) := by
  let hA := A.property.diag_isZero i
  let hM := M.property.diag_isZero i
  let hN := N.property.diag_isZero i
  let hfIso : IsIso (f.hom.app (diag i)) := hA.isIso hM _
  let hinrIso : IsIso (P.inr.app (diag i)) :=
    (P.isPushout_app (diag i)).isIso_inr_of_isIso hfIso
  let e : N.obj.obj (diag i) ≅ P.apex.obj (diag i) :=
    @asIso C _ _ _ (P.inr.app (diag i)) hinrIso
  exact IsZero.of_iso hN e.symm

/-- One successor zero-row map in the apex is a cofibration. -/
private theorem zeroRowSucc_isCofibration
    (P : StagePushoutPresentation C f g)
    (hf : stageCofibrations C n f) (r : Fin n) :
    IsCofibration
      (P.apex.map (horiz (Fin.zero_le _) r.castSucc_le_succ)) := by
  let I₀ : Ar n := interval 0 r.castSucc (Fin.zero_le _)
  let I₁ : Ar n := interval 0 r.succ (Fin.zero_le _)
  let h : I₀ ⟶ I₁ := horiz (Fin.zero_le _) r.castSucc_le_succ
  obtain ⟨K, kA, kM, d, hK, hkA, hkM, hd⟩ := hf r
  change A.obj.obj I₁ ⟶ K at kA
  change M.obj.obj I₀ ⟶ K at kM
  change K ⟶ M.obj.obj I₁ at d
  change IsPushout (A.obj.map h) (f.hom.app I₀) kA kM at hK
  change kA ≫ d = f.hom.app I₁ at hkA
  change kM ≫ d = M.obj.map h at hkM
  change IsCofibration d at hd
  let nMap : N.obj.obj I₀ ⟶ N.obj.obj I₁ := N.obj.map h
  have hn : IsCofibration nMap := by
    change IsCofibration
      (N.obj.map (horiz (Fin.zero_le _) r.castSucc_le_succ))
    exact (N.property.cofiber_triple (Fin.zero_le _)
      r.castSucc_le_succ).1
  have hnAdm : ExactCategory.IsAdmissibleMono nMap := by
    change ExactCategory.IsAdmissibleMono nMap at hn
    exact hn
  obtain ⟨V, u, vN, hV, hu⟩ :=
    ExactCategory.admissibleMono_pushout
      (X := N.obj.obj I₀) (Y := N.obj.obj I₁)
      (i := nMap) hnAdm
      (X' := P.apex.obj I₀) (f := P.inr.app I₀)
  let q : K ⟶ V := hK.desc
    (g.hom.app I₁ ≫ vN) (P.inl.app I₀ ≫ u) (by
      calc
        A.obj.map h ≫ (g.hom.app I₁ ≫ vN) =
            (A.obj.map h ≫ g.hom.app I₁) ≫ vN :=
              (Category.assoc _ _ _).symm
        _ = (g.hom.app I₀ ≫ nMap) ≫ vN := by
              rw [g.hom.naturality h]
        _ = g.hom.app I₀ ≫ (nMap ≫ vN) := Category.assoc _ _ _
        _ = g.hom.app I₀ ≫ (P.inr.app I₀ ≫ u) := by rw [← hV.w]
        _ = (g.hom.app I₀ ≫ P.inr.app I₀) ≫ u :=
              (Category.assoc _ _ _).symm
        _ = (f.hom.app I₀ ≫ P.inl.app I₀) ≫ u := by
              rw [(P.isPushout_app I₀).w]
        _ = f.hom.app I₀ ≫ (P.inl.app I₀ ≫ u) :=
              Category.assoc _ _ _)
  have hqA : kA ≫ q = g.hom.app I₁ ≫ vN :=
    hK.inl_desc _ _ _
  have hqM : kM ≫ q = P.inl.app I₀ ≫ u :=
    hK.inr_desc _ _ _
  let b : P.apex.obj I₀ ⟶ P.apex.obj I₁ := P.apex.map h
  let v : V ⟶ P.apex.obj I₁ := hV.desc b (P.inr.app I₁) (by
    change P.inr.app I₀ ≫ P.apex.map h = nMap ≫ P.inr.app I₁
    exact (P.inr.naturality h).symm)
  have huV : u ≫ v = b := hV.inl_desc _ _ _
  have hvN : vN ≫ v = P.inr.app I₁ := hV.inr_desc _ _ _
  have hcomm : d ≫ P.inl.app I₁ = q ≫ v := by
    apply hK.hom_ext
    · calc
        kA ≫ (d ≫ P.inl.app I₁) =
            (kA ≫ d) ≫ P.inl.app I₁ := (Category.assoc _ _ _).symm
        _ = f.hom.app I₁ ≫ P.inl.app I₁ :=
          congrArg (fun z => z ≫ P.inl.app I₁) hkA
        _ = g.hom.app I₁ ≫ P.inr.app I₁ := (P.isPushout_app I₁).w
        _ = g.hom.app I₁ ≫ (vN ≫ v) := by rw [hvN]
        _ = (g.hom.app I₁ ≫ vN) ≫ v := (Category.assoc _ _ _).symm
        _ = (kA ≫ q) ≫ v := congrArg (fun z => z ≫ v) hqA.symm
        _ = kA ≫ (q ≫ v) := Category.assoc _ _ _
    · calc
        kM ≫ (d ≫ P.inl.app I₁) =
            (kM ≫ d) ≫ P.inl.app I₁ := (Category.assoc _ _ _).symm
        _ = M.obj.map h ≫ P.inl.app I₁ :=
          congrArg (fun z => z ≫ P.inl.app I₁) hkM
        _ = P.inl.app I₀ ≫ b := P.inl.naturality h
        _ = P.inl.app I₀ ≫ (u ≫ v) := by rw [huV]
        _ = (P.inl.app I₀ ≫ u) ≫ v := (Category.assoc _ _ _).symm
        _ = (kM ≫ q) ≫ v := congrArg (fun z => z ≫ v) hqM.symm
        _ = kM ≫ (q ≫ v) := Category.assoc _ _ _
  have compat (s : PushoutCocone d q) :
      f.hom.app I₁ ≫ s.inl = g.hom.app I₁ ≫ (vN ≫ s.inr) := by
    calc
      f.hom.app I₁ ≫ s.inl = (kA ≫ d) ≫ s.inl :=
        congrArg (fun z => z ≫ s.inl) hkA.symm
      _ = kA ≫ (d ≫ s.inl) := Category.assoc _ _ _
      _ = kA ≫ (q ≫ s.inr) := by rw [s.condition]
      _ = (kA ≫ q) ≫ s.inr := (Category.assoc _ _ _).symm
      _ = (g.hom.app I₁ ≫ vN) ≫ s.inr := by rw [hqA]
      _ = g.hom.app I₁ ≫ (vN ≫ s.inr) := Category.assoc _ _ _
  let lift (s : PushoutCocone d q) : P.apex.obj I₁ ⟶ s.pt :=
    (P.isPushout_app I₁).desc s.inl (vN ≫ s.inr) (compat s)
  have lift_inl (s : PushoutCocone d q) :
      P.inl.app I₁ ≫ lift s = s.inl := by
    exact (P.isPushout_app I₁).inl_desc _ _ _
  have lift_inr (s : PushoutCocone d q) :
      P.inr.app I₁ ≫ lift s = vN ≫ s.inr := by
    exact (P.isPushout_app I₁).inr_desc _ _ _
  have hKV : IsPushout d q (P.inl.app I₁) v := by
    refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hcomm) ?_
    refine PushoutCocone.IsColimit.mk hcomm lift ?_ ?_ ?_
    · exact lift_inl
    · intro s
      apply hV.hom_ext
      · apply (P.isPushout_app I₀).hom_ext
        · calc
            P.inl.app I₀ ≫ (u ≫ (v ≫ lift s)) =
                (P.inl.app I₀ ≫ u) ≫ (v ≫ lift s) :=
              (Category.assoc _ _ _).symm
            _ = (kM ≫ q) ≫ (v ≫ lift s) := by rw [hqM]
            _ = kM ≫ ((q ≫ v) ≫ lift s) := by simp only [Category.assoc]
            _ = kM ≫ ((d ≫ P.inl.app I₁) ≫ lift s) := by rw [hcomm]
            _ = kM ≫ (d ≫ (P.inl.app I₁ ≫ lift s)) := by
              simp only [Category.assoc]
            _ = kM ≫ (d ≫ s.inl) := by rw [lift_inl]
            _ = kM ≫ (q ≫ s.inr) := by rw [s.condition]
            _ = (kM ≫ q) ≫ s.inr := (Category.assoc _ _ _).symm
            _ = (P.inl.app I₀ ≫ u) ≫ s.inr := by rw [hqM]
            _ = P.inl.app I₀ ≫ (u ≫ s.inr) := Category.assoc _ _ _
        · calc
            P.inr.app I₀ ≫ (u ≫ (v ≫ lift s)) =
                (P.inr.app I₀ ≫ u) ≫ (v ≫ lift s) :=
              (Category.assoc _ _ _).symm
            _ = (nMap ≫ vN) ≫ (v ≫ lift s) := by rw [hV.w]
            _ = nMap ≫ ((vN ≫ v) ≫ lift s) := by simp only [Category.assoc]
            _ = nMap ≫ (P.inr.app I₁ ≫ lift s) := by rw [hvN]
            _ = nMap ≫ (vN ≫ s.inr) := by rw [lift_inr]
            _ = (nMap ≫ vN) ≫ s.inr := (Category.assoc _ _ _).symm
            _ = (P.inr.app I₀ ≫ u) ≫ s.inr := by rw [hV.w]
            _ = P.inr.app I₀ ≫ (u ≫ s.inr) := Category.assoc _ _ _
      · calc
          vN ≫ (v ≫ lift s) = (vN ≫ v) ≫ lift s :=
            (Category.assoc _ _ _).symm
          _ = P.inr.app I₁ ≫ lift s := by rw [hvN]
          _ = vN ≫ s.inr := lift_inr s
    · intro s m hm₁ hm₂
      apply (P.isPushout_app I₁).hom_ext
      · exact hm₁.trans (lift_inl s).symm
      · calc
          P.inr.app I₁ ≫ m = (vN ≫ v) ≫ m := by rw [hvN]
          _ = vN ≫ (v ≫ m) := Category.assoc _ _ _
          _ = vN ≫ s.inr := by rw [hm₂]
          _ = P.inr.app I₁ ≫ lift s := (lift_inr s).symm
  have hdAdm : ExactCategory.IsAdmissibleMono d := by
    change ExactCategory.IsAdmissibleMono d at hd
    exact hd
  have hvAdm : ExactCategory.IsAdmissibleMono v :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (P := admissibleMonosOf C ExactCategory.IsAdmissibleExact)
      hKV.flip hdAdm
  have hbAdm : ExactCategory.IsAdmissibleMono b := by
    rw [← huV]
    exact ExactCategory.admissibleMono_comp.comp_mem u v hu hvAdm
  change ExactCategory.IsAdmissibleMono (P.apex.map h)
  exact hbAdm

/-- Successor cofibrations imply cofibrations on all zero-row intervals. -/
private theorem zeroRowMap_isAdmissibleMono
    (B : Ar n ⥤ C)
    (hB : ∀ r : Fin n,
      ExactCategory.IsAdmissibleMono
        (B.map (horiz (Fin.zero_le _) r.castSucc_le_succ)))
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    ExactCategory.IsAdmissibleMono
      (B.map (horiz (Fin.zero_le _) hij)) := by
  revert i
  induction j using Fin.induction with
  | zero =>
      intro i hij
      obtain rfl : i = 0 := le_antisymm hij (Fin.zero_le i)
      have heq : horiz (Fin.zero_le _) hij =
          𝟙 (interval 0 0 (Fin.zero_le _)) := by
        apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
      rw [heq, Functor.map_id]
      exact ExactCategory.isAdmissibleMono_id _
  | succ j ih =>
      intro i hij
      by_cases hi : i = j.succ
      · subst i
        have heq : horiz (Fin.zero_le _) hij =
            𝟙 (interval 0 j.succ (Fin.zero_le _)) := by
          apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
        rw [heq, Functor.map_id]
        exact ExactCategory.isAdmissibleMono_id _
      · have hneVal : i.val ≠ j.val + 1 := by
          intro hval
          apply hi
          apply Fin.ext
          exact hval
        have hij' : i ≤ j.castSucc := by
          change i.val ≤ j.val
          change i.val ≤ j.val + 1 at hij
          omega
        have hcomp : horiz (Fin.zero_le _) hij =
            horiz (Fin.zero_le _) hij' ≫
              horiz (Fin.zero_le _) j.castSucc_le_succ := by
          apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
        rw [hcomp, Functor.map_comp]
        exact ExactCategory.admissibleMono_comp.comp_mem _ _
          (ih hij') (hB j)

/-- The length-two pointwise pushout data on a stage triple. -/
private def tripleData (P : StagePushoutPresentation C f g)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    LevelwisePushoutData C := by
  let I₀ : Ar n := interval i j hij
  let I₁ : Ar n := interval i k (hij.trans hjk)
  let I₂ : Ar n := interval j k hjk
  let h₀₁ : I₀ ⟶ I₁ := horiz hij hjk
  let h₁₂ : I₁ ⟶ I₂ := vert hij hjk
  exact
    { R := ComposableArrows.mk₂ (A.obj.map h₀₁) (A.obj.map h₁₂)
      S := ComposableArrows.mk₂ (M.obj.map h₀₁) (M.obj.map h₁₂)
      T := ComposableArrows.mk₂ (N.obj.map h₀₁) (N.obj.map h₁₂)
      RS := ComposableArrows.homMk₂
        (f.hom.app I₀) (f.hom.app I₁) (f.hom.app I₂)
        (f.hom.naturality h₀₁) (f.hom.naturality h₁₂)
      RT := ComposableArrows.homMk₂
        (g.hom.app I₀) (g.hom.app I₁) (g.hom.app I₂)
        (g.hom.naturality h₀₁) (g.hom.naturality h₁₂)
      P0 := P.apex.obj I₀
      P1 := P.apex.obj I₁
      P2 := P.apex.obj I₂
      inlS0 := P.inl.app I₀
      inrT0 := P.inr.app I₀
      inlS1 := P.inl.app I₁
      inrT1 := P.inr.app I₁
      inlS2 := P.inl.app I₂
      inrT2 := P.inr.app I₂
      isPushout0 := P.isPushout_app I₀
      isPushout1 := P.isPushout_app I₁
      isPushout2 := P.isPushout_app I₂ }

private theorem tripleData_inducedMap01
    (P : StagePushoutPresentation C f g)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (tripleData P hij hjk).inducedMap01 =
      P.apex.map (horiz hij hjk) := by
  let D := tripleData P hij hjk
  apply D.isPushout0.hom_ext
  · exact D.inl_map01.trans (P.inl.naturality (horiz hij hjk))
  · exact D.inr_map01.trans (P.inr.naturality (horiz hij hjk))

private theorem tripleData_inducedMap12
    (P : StagePushoutPresentation C f g)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (tripleData P hij hjk).inducedMap12 =
      P.apex.map (vert hij hjk) := by
  let D := tripleData P hij hjk
  apply D.isPushout1.hom_ext
  · exact D.inl_map12.trans (P.inl.naturality (vert hij hjk))
  · exact D.inr_map12.trans (P.inr.naturality (vert hij hjk))

/-- Every zero-row triple of the apex is a cofiber sequence. -/
private theorem zeroRow_cofiber (P : StagePushoutPresentation C f g)
    (hf : stageCofibrations C n f)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsCofibrationSequence
      (P.apex.map (horiz (Fin.zero_le _) hij))
      (P.apex.map (vert (Fin.zero_le _) hij)) := by
  let D := tripleData P (Fin.zero_le i) hij
  have hM := M.property.cofiber_triple (Fin.zero_le i) hij
  have hN := N.property.cofiber_triple (Fin.zero_le i) hij
  have hA := A.property.cofiber_triple (Fin.zero_le i) hij
  let wM : D.S.map' 0 1 ≫ D.S.map' 1 2 = 0 := by
    change M.obj.map (horiz (Fin.zero_le i) hij) ≫
      M.obj.map (vert (Fin.zero_le i) hij) = 0
    exact hM.comp_eq_zero
  let wN : D.T.map' 0 1 ≫ D.T.map' 1 2 = 0 := by
    change N.obj.map (horiz (Fin.zero_le i) hij) ≫
      N.obj.map (vert (Fin.zero_le i) hij) = 0
    exact hN.comp_eq_zero
  have hMAdm : ExactCategory.IsAdmissibleExact
      (ShortComplex.mk (D.S.map' 0 1) (D.S.map' 1 2) wM) :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence hM
  have hNAdm : ExactCategory.IsAdmissibleExact
      (ShortComplex.mk (D.T.map' 0 1) (D.T.map' 1 2) wN) :=
    ExactCategory.isAdmissibleExact_of_isCofibrationSequence hN
  let _ : Epi (D.R.map' 1 2) := by
    have hAAdm : ExactCategory.IsAdmissibleExact
        (ShortComplex.mk (D.R.map' 0 1) (D.R.map' 1 2) (by
          change A.obj.map (horiz (Fin.zero_le i) hij) ≫
            A.obj.map (vert (Fin.zero_le i) hij) = 0
          exact hA.comp_eq_zero)) :=
      ExactCategory.isAdmissibleExact_of_isCofibrationSequence hA
    exact (ExactCategory.isAdmissibleEpi_g hAAdm).epi
  have hc := levelwisePushoutShortComplex_isColimit_cokernel C D wM wN
    (ExactCategory.isColimit_cokernelCofork_of_isAdmissibleExact hMAdm)
    (ExactCategory.isColimit_cokernelCofork_of_isAdmissibleExact hNAdm)
  have hm : ExactCategory.IsAdmissibleMono D.inducedMap01 := by
    rw [tripleData_inducedMap01]
    change IsCofibration
      (P.apex.map (horiz (Fin.zero_le _) hij))
    exact zeroRowMap_isAdmissibleMono P.apex
      (fun r => zeroRowSucc_isCofibration P hf r) hij
  have hAdm : ExactCategory.IsAdmissibleExact
      (levelwisePushoutShortComplex C D wM wN) :=
    ExactCategory.isAdmissibleExact_of_isAdmissibleMono_isColimit hm hc
  have hSeq := isCofibrationSequence_levelwisePushout C D wM wN hAdm
  rw [tripleData_inducedMap01, tripleData_inducedMap12] at hSeq
  exact hSeq

/-- Transport a chosen-zero cofiber square to its actual zero diagonal. -/
private theorem actualSquare_of_isZero_of_cofiber
    (B : Ar n ⥤ C) {i j k : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k)
    (hZero : IsZero (B.obj (diag j)))
    (hSeq : IsCofibrationSequence
      (B.map (horiz hij hjk)) (B.map (vert hij hjk))) :
    IsPushout (B.map (horiz hij hjk)) (B.map (toDiag hij))
      (B.map (vert hij hjk)) (B.map (fromDiag hjk)) := by
  obtain ⟨_, h, q, hpush⟩ := hSeq
  have hflip := hpush.flip
  let e : (0 : C) ≅ B.obj (diag j) := (isZero_zero _).iso hZero
  apply hflip.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp
  · simpa using hZero.eq_of_tgt _ _
  · simp
  · simpa using (isZero_zero _).eq_of_src _ _

/-- A functorial pointwise pushout along a genuine stage cofibration is a
finite Waldhausen stage. -/
theorem isStage_of_stageCofibration (P : StagePushoutPresentation C f g)
    (hf : stageCofibrations C n f) : IsStage n P.apex := by
  refine { diag_isZero := apex_diag_isZero P, cofiber_triple := ?_ }
  intro i j k hij hjk
  have hZeroI := apex_diag_isZero P i
  have hZeroJ := apex_diag_isZero P j
  have hIJ := zeroRow_cofiber P hf hij
  have hIK := zeroRow_cofiber P hf (hij.trans hjk)
  have hJK := zeroRow_cofiber P hf hjk
  have pIJ := actualSquare_of_isZero_of_cofiber P.apex
    (Fin.zero_le i) hij hZeroI hIJ
  have pIK := actualSquare_of_isZero_of_cofiber P.apex
    (Fin.zero_le i) (hij.trans hjk) hZeroI hIK
  have pJK := actualSquare_of_isZero_of_cofiber P.apex
    (Fin.zero_le j) hjk hZeroJ hJK
  have hTop :
      P.apex.map (horiz (Fin.zero_le i) hij) ≫
          P.apex.map (horiz (Fin.zero_le j) hjk) =
        P.apex.map (horiz (Fin.zero_le i) (hij.trans hjk)) := by
    rw [← P.apex.map_comp]
    congr 1
  have hBottom :
      P.apex.map (fromDiag hij) ≫ P.apex.map (horiz hij hjk) =
        P.apex.map (fromDiag (hij.trans hjk)) := by
    rw [← P.apex.map_comp]
    congr 1
  have pIK' : IsPushout
      (P.apex.map (horiz (Fin.zero_le i) hij) ≫
        P.apex.map (horiz (Fin.zero_le j) hjk))
      (P.apex.map (toDiag (Fin.zero_le i)))
      (P.apex.map (vert (Fin.zero_le i) (hij.trans hjk)))
      (P.apex.map (fromDiag hij) ≫
        P.apex.map (horiz hij hjk)) := by
    rw [hTop, hBottom]
    exact pIK
  have hRightComm :
      P.apex.map (horiz (Fin.zero_le j) hjk) ≫
          P.apex.map (vert (Fin.zero_le i) (hij.trans hjk)) =
        P.apex.map (vert (Fin.zero_le i) hij) ≫
          P.apex.map (horiz hij hjk) := by
    rw [← P.apex.map_comp, ← P.apex.map_comp]
    congr 1
  have pRight : IsPushout
      (P.apex.map (horiz (Fin.zero_le j) hjk))
      (P.apex.map (vert (Fin.zero_le i) hij))
      (P.apex.map (vert (Fin.zero_le i) (hij.trans hjk)))
      (P.apex.map (horiz hij hjk)) := by
    exact pIK'.of_left hRightComm pIJ
  have hOuterLeft :
      P.apex.map (vert (Fin.zero_le i) hij) ≫
          P.apex.map (toDiag hij) =
        P.apex.map (toDiag (Fin.zero_le j)) := by
    rw [← P.apex.map_comp]
    congr 1
  have hOuterRight :
      P.apex.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫
          P.apex.map (vert hij hjk) =
        P.apex.map (vert (Fin.zero_le j) hjk) := by
    rw [← P.apex.map_comp]
    congr 1
  have pJK' : IsPushout
      (P.apex.map (horiz (Fin.zero_le j) hjk))
      (P.apex.map (vert (Fin.zero_le i) hij) ≫
        P.apex.map (toDiag hij))
      (P.apex.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫
        P.apex.map (vert hij hjk))
      (P.apex.map (fromDiag hjk)) := by
    rw [hOuterLeft, hOuterRight]
    exact pJK
  have hDesiredComm :
      P.apex.map (horiz hij hjk) ≫ P.apex.map (vert hij hjk) =
        P.apex.map (toDiag hij) ≫ P.apex.map (fromDiag hjk) := by
    rw [← P.apex.map_comp, ← P.apex.map_comp]
    congr 1
  have pDesired : IsPushout
      (P.apex.map (horiz hij hjk))
      (P.apex.map (toDiag hij))
      (P.apex.map (vert hij hjk))
      (P.apex.map (fromDiag hjk)) := by
    exact pJK'.of_top hDesiredComm pRight
  have hZeroRow : IsCofibration
      (P.apex.map (horiz (Fin.zero_le j) hjk)) :=
    (zeroRow_cofiber P hf hjk).1
  have hFirst : IsCofibration (P.apex.map (horiz hij hjk)) := by
    change ExactCategory.IsAdmissibleMono _ at hZeroRow ⊢
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (P := admissibleMonosOf C ExactCategory.IsAdmissibleExact)
      pRight.flip hZeroRow
  let e : (0 : C) ≅ P.apex.obj (diag j) := (isZero_zero _).iso hZeroJ
  have pChosen : IsPushout
      (0 : P.apex.obj (interval i j hij) ⟶ (0 : C))
      (P.apex.map (horiz hij hjk))
      (0 : (0 : C) ⟶ P.apex.obj (interval j k hjk))
      (P.apex.map (vert hij hjk)) := by
    apply pDesired.flip.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    · exact (isZero_zero C).eq_of_tgt _ _
    · simp
    · simpa using hZeroJ.eq_of_src _ _
    · simp
  exact ⟨hFirst, (0 : _ ⟶ (0 : C)), (0 : (0 : C) ⟶ _), pChosen⟩

/-- Bundle the apex of a stage-pushout presentation as a stage. -/
def toStage (P : StagePushoutPresentation C f g)
    (hf : stageCofibrations C n f) : Stage C n :=
  ⟨P.apex, P.isStage_of_stageCofibration hf⟩

end StagePushoutPresentation

end CategoryTheory.Waldhausen.SConstruction
