/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Zero
public import MathlibExt.CategoryTheory.ExactCategory.PushoutFlag
public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Quotient-completed Stages from admissible-mono flags

A zero-based finite flag whose successor maps are admissible monomorphisms
determines a finite Waldhausen Stage.  Quotient objects are constructed one
row at a time: the next cell is the pushout of the new filtration mono along
the preceding row quotient.  Interval maps are then the canonical maps
between these cokernels.

This file installs no global limit, exact, or Waldhausen instance and makes no
Quillen, nerve, realization, or K-theory claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- A zero-based composable flag with admissible-mono successor maps. -/
structure AdmissibleMonoFlag (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] (n : ℕ) where
  /-- Underlying finite chain. -/
  chain : ComposableArrows C n
  /-- Its first object is zero. -/
  first_isZero : IsZero (chain.obj 0)
  /-- Every successor map is an admissible mono. -/
  step_admissible : ∀ (i : ℕ) (hi : i < n),
    IsAdmissibleMono
      (chain.map' i (i + 1) (Nat.le_succ i) (Nat.succ_le_iff.mpr hi))

namespace AdmissibleMonoFlag

/-- Implementation presentation data for a quotient of one admissible mono.  The
public interface below is given by `intervalQuotient`, `intervalπ`, and their
characteristic laws. -/
structure IntervalQuotientData {X Y : C} (f : X ⟶ Y) where
  quotient : C
  π : Y ⟶ quotient
  zero : f ≫ π = 0
  exact : IsAdmissibleExact (ShortComplex.mk f π zero)

namespace IntervalQuotientData

private noncomputable def ofMono {X Y : C} {f : X ⟶ Y}
    (hf : IsAdmissibleMono f) : IntervalQuotientData f := by
  choose Q p w h using hf
  exact ⟨Q, p, w, h⟩

private noncomputable def cast {X Y : C} {f g : X ⟶ Y}
    (h : f = g) (D : IntervalQuotientData f) : IntervalQuotientData g := by
  subst h
  exact D

/-- Extend one quotient row by pushing out the new filtration mono along the
preceding quotient map. -/
private noncomputable def pushoutStep
    {K A Y : C} {i : K ⟶ A} {r : A ⟶ Y}
    (D : IntervalQuotientData i) (E : IntervalQuotientData r)
    (hr : IsAdmissibleMono r) : IntervalQuotientData (i ≫ r) := by
  letI : HasPushout r D.π :=
    hasPushout_ofHasPushoutsAgainst
      (P := admissibleMonosOf C IsAdmissibleExact) hr
      (show (⊤ : MorphismProperty C) D.π from trivial)
  let sq : IsPushout D.π r (pushout.inr r D.π) (pushout.inl r D.π) :=
    (IsPushout.of_hasPushout r D.π).flip
  exact ⟨pushout r D.π, pushout.inl r D.π,
    by
      rw [Category.assoc, ← sq.w, ← Category.assoc, D.zero, zero_comp],
    isAdmissibleExact_comp_pushout i D.π r E.π
      (pushout.inr r D.π) (pushout.inl r D.π)
      D.zero E.zero D.exact E.exact sq⟩

end IntervalQuotientData

variable {n : ℕ} (F : AdmissibleMonoFlag C n)

/-- Inductively quotient-complete the row starting at `i` and ending at
`j`.  Successor cells are literal pushouts of the preceding quotient. -/
@[no_expose]
noncomputable def intervalData (j : Fin (n + 1)) :
    ∀ (i : Fin (n + 1)) (hij : i ≤ j),
      IntervalQuotientData (F.chain.map (homOfLE hij)) := by
  induction j using Fin.induction with
  | zero =>
      intro i hi
      have hieq : i = 0 := le_antisymm hi (Fin.zero_le i)
      subst i
      let D := IntervalQuotientData.ofMono
        (IsAdmissibleMono.id (F.chain.obj 0))
      have hmap : F.chain.map (homOfLE (le_refl (0 : Fin (n + 1)))) =
          𝟙 (F.chain.obj 0) := by
        rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
      exact IntervalQuotientData.cast hmap.symm D
  | succ j ih =>
      intro i hi
      by_cases heq : i = j.succ
      · subst i
        let D := IntervalQuotientData.ofMono
          (IsAdmissibleMono.id (F.chain.obj j.succ))
        have hmap : F.chain.map (homOfLE (le_refl j.succ)) =
            𝟙 (F.chain.obj j.succ) := by
          rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
        exact IntervalQuotientData.cast hmap.symm D
      · have hip : i ≤ j.castSucc := by
          have hilt : i < j.succ := lt_of_le_of_ne hi heq
          have hval : i.val < j.val + 1 := by
            simpa only [Fin.lt_def, Fin.val_succ] using hilt
          rw [Fin.le_iff_val_le_val]
          exact Nat.lt_succ_iff.mp hval
        let D := ih i hip
        have hjlt : j.val < n := j.isLt
        have hs : j.castSucc ≤ j.succ := by
          rw [Fin.le_iff_val_le_val]
          simp
        have hmono : IsAdmissibleMono
            (F.chain.map (homOfLE hs)) := by
          change IsAdmissibleMono
            (F.chain.map' j.val (j.val + 1) (Nat.le_succ j.val)
              (Nat.succ_le_iff.mpr hjlt))
          exact F.step_admissible j.val hjlt
        let E := IntervalQuotientData.ofMono hmono
        let P := IntervalQuotientData.pushoutStep D E hmono
        have hcomp : F.chain.map (homOfLE hi) =
            F.chain.map (homOfLE hip) ≫
              F.chain.map (homOfLE hs) := by
          rw [← F.chain.map_comp]
          congr
        exact IntervalQuotientData.cast hcomp.symm P

/-- Quotient object attached to an interval of the flag.  For fixed left
endpoint these objects are constructed successively by pushouts. -/
noncomputable abbrev intervalQuotient
    (i j : Fin (n + 1)) (hij : i ≤ j) : C :=
  (intervalData F j i hij).quotient

/-- Projection from the right endpoint of a flag interval to its quotient. -/
noncomputable abbrev intervalπ
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    F.chain.obj j ⟶ F.intervalQuotient i j hij :=
  (intervalData F j i hij).π

/-- The composite flag mono followed by its interval projection is zero. -/
@[reassoc (attr := simp)]
theorem interval_comp_π
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    F.chain.map (homOfLE hij) ≫ F.intervalπ i j hij = 0 :=
  (intervalData F j i hij).zero

/-- Every interval projection completes its composite flag mono to an
admissible exact sequence. -/
theorem interval_exact
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE hij))
        (F.intervalπ i j hij) (F.interval_comp_π i j hij)) :=
  (intervalData F j i hij).exact

/-- Compare the inductively constructed interval quotient with any other
admissible-exact quotient of the same composite flag mono. -/
noncomputable def intervalIsoOfExact
    {i j : Fin (n + 1)} (hij : i ≤ j)
    {Q : C} (q : F.chain.obj j ⟶ Q)
    (w : F.chain.map (homOfLE hij) ≫ q = 0)
    (h : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE hij)) q w)) :
    F.intervalQuotient i j hij ≅ Q :=
  (isColimit_cokernelCofork_of_isAdmissibleExact
    (F.interval_exact i j hij)).coconePointUniqueUpToIso
      (isColimit_cokernelCofork_of_isAdmissibleExact
        (S := ShortComplex.mk (F.chain.map (homOfLE hij)) q w) h)

/-- The interval projection followed by the quotient comparison is the given
quotient map. -/
@[reassoc (attr := simp)]
theorem intervalπ_intervalIsoOfExact_hom
    {i j : Fin (n + 1)} (hij : i ≤ j)
    {Q : C} (q : F.chain.obj j ⟶ Q)
    (w : F.chain.map (homOfLE hij) ≫ q = 0)
    (h : IsAdmissibleExact
      (ShortComplex.mk (F.chain.map (homOfLE hij)) q w)) :
    F.intervalπ i j hij ≫ (F.intervalIsoOfExact hij q w h).hom = q := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimit_cokernelCofork_of_isAdmissibleExact
      (F.interval_exact i j hij))
    (isColimit_cokernelCofork_of_isAdmissibleExact
      (S := ShortComplex.mk (F.chain.map (homOfLE hij)) q w) h)
    WalkingParallelPair.one

/-- Canonical map between interval quotients induced by increasing both
endpoints. -/
noncomputable def intervalMap
    {i j i' j' : Fin (n + 1)}
    (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    F.intervalQuotient i j hij ⟶
      F.intervalQuotient i' j' hi'j' := by
  let D := intervalData F j i hij
  let D' := intervalData F j' i' hi'j'
  let m := F.chain.map (homOfLE hjj')
  have hz : F.chain.map (homOfLE hij) ≫ (m ≫ D'.π) = 0 := by
    rw [← Category.assoc, ← F.chain.map_comp]
    have hpaths : (homOfLE hij : i ⟶ j) ≫ homOfLE hjj' =
        homOfLE hii' ≫ homOfLE hi'j' := Subsingleton.elim _ _
    rw [hpaths, F.chain.map_comp, Category.assoc, D'.zero, comp_zero]
  exact (isColimit_cokernelCofork_of_isAdmissibleExact D.exact).desc
    (CokernelCofork.ofπ (m ≫ D'.π) hz)

/-- Interval maps compute after the source quotient projection. -/
@[reassoc (attr := simp)]
theorem intervalπ_naturality
    {i j i' j' : Fin (n + 1)}
    (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    F.intervalπ i j hij ≫ F.intervalMap hij hi'j' hii' hjj' =
      F.chain.map (homOfLE hjj') ≫ F.intervalπ i' j' hi'j' := by
  exact Cofork.IsColimit.π_desc
    (isColimit_cokernelCofork_of_isAdmissibleExact
      (intervalData F j i hij).exact)

/-- Quotienting a longer filtration interval is the pushout of the new flag
segment along the shorter quotient projection. -/
theorem intervalSquare_isPushout
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      (F.intervalπ i j hij)
      (F.chain.map (homOfLE hjk))
      (F.intervalMap hij (hij.trans hjk) le_rfl hjk)
      (F.intervalπ i k (hij.trans hjk)) := by
  let Dik := intervalData F k i (hij.trans hjk)
  let Dij := intervalData F j i hij
  let f := F.chain.map (homOfLE hjk)
  let x := F.intervalMap hij (hij.trans hjk) le_rfl hjk
  change IsPushout Dij.π f x Dik.π
  have hw : Dij.π ≫ x = f ≫ Dik.π :=
    F.intervalπ_naturality hij (hij.trans hjk) le_rfl hjk
  let hz (s : PushoutCocone Dij.π f) :
      F.chain.map (homOfLE (hij.trans hjk)) ≫ s.inr = 0 := by
    calc
      F.chain.map (homOfLE (hij.trans hjk)) ≫ s.inr =
          (F.chain.map (homOfLE hij) ≫
            F.chain.map (homOfLE hjk)) ≫ s.inr := by
              rw [← F.chain.map_comp]
              congr
      _ = F.chain.map (homOfLE hij) ≫
          (F.chain.map (homOfLE hjk) ≫ s.inr) :=
            Category.assoc _ _ _
      _ = F.chain.map (homOfLE hij) ≫
          (Dij.π ≫ s.inl) := by rw [s.condition]
      _ = (F.chain.map (homOfLE hij) ≫ Dij.π) ≫ s.inl :=
            (Category.assoc _ _ _).symm
      _ = 0 := by rw [Dij.zero, zero_comp]
  let hc : IsColimit (CokernelCofork.ofπ Dik.π Dik.zero) := by
    simpa only using
      isColimit_cokernelCofork_of_isAdmissibleExact Dik.exact
  let d (s : PushoutCocone Dij.π f) : Dik.quotient ⟶ s.pt :=
    hc.desc (CokernelCofork.ofπ s.inr (hz s))
  refine { w := hw, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.IsColimit.mk hw
    d (fun s => ?_) (fun s => ?_)
    (fun s m hm₁ hm₂ => ?_)
  · let : Epi Dij.π := (isAdmissibleEpi_g Dij.exact).epi
    apply (cancel_epi Dij.π).1
    rw [← Category.assoc, hw, Category.assoc]
    change f ≫ (Dik.π ≫ d s) = _
    rw [show Dik.π ≫ d s = s.inr from
      Cofork.IsColimit.π_desc hc]
    exact s.condition.symm
  · change Dik.π ≫ d s = s.inr
    dsimp only [d]
    have hd := Cofork.IsColimit.π_desc hc
      (t := CokernelCofork.ofπ s.inr (hz s))
    rw [Cofork.π_ofπ] at hd
    exact hd
  · let : Epi Dik.π := (isAdmissibleEpi_g Dik.exact).epi
    apply (cancel_epi Dik.π).1
    dsimp only [d]
    have hd := Cofork.IsColimit.π_desc hc
      (t := CokernelCofork.ofπ s.inr (hz s))
    rw [Cofork.π_ofπ] at hd
    exact hm₂.trans hd.symm

/-- The two canonical legs attached to nested intervals compose to zero. -/
@[reassoc (attr := simp)]
theorem intervalMap_comp_eq_zero
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    F.intervalMap hij (hij.trans hjk) le_rfl hjk ≫
      F.intervalMap (hij.trans hjk) hjk hij le_rfl = 0 := by
  let : Epi (F.intervalπ i j hij) :=
    (isAdmissibleEpi_g (F.interval_exact i j hij)).epi
  apply (cancel_epi (F.intervalπ i j hij)).1
  calc
    F.intervalπ i j hij ≫
        (F.intervalMap hij (hij.trans hjk) le_rfl hjk ≫
          F.intervalMap (hij.trans hjk) hjk hij le_rfl) =
      (F.intervalπ i j hij ≫
        F.intervalMap hij (hij.trans hjk) le_rfl hjk) ≫
          F.intervalMap (hij.trans hjk) hjk hij le_rfl :=
        (Category.assoc _ _ _).symm
    _ = (F.chain.map (homOfLE hjk) ≫
        F.intervalπ i k (hij.trans hjk)) ≫
          F.intervalMap (hij.trans hjk) hjk hij le_rfl := by
        rw [F.intervalπ_naturality hij (hij.trans hjk) le_rfl hjk]
    _ = F.chain.map (homOfLE hjk) ≫
        (F.intervalπ i k (hij.trans hjk) ≫
          F.intervalMap (hij.trans hjk) hjk hij le_rfl) :=
        Category.assoc _ _ _
    _ = F.chain.map (homOfLE hjk) ≫ F.intervalπ j k hjk := by
        rw [F.intervalπ_naturality (hij.trans hjk) hjk hij le_rfl]
        simp
    _ = 0 := F.interval_comp_π j k hjk
    _ = F.intervalπ i j hij ≫ 0 := by simp

/-- Every triple of interval quotients is an admissible exact sequence. -/
theorem interval_triple_exact
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    IsAdmissibleExact
      (ShortComplex.mk
        (F.intervalMap hij (hij.trans hjk) le_rfl hjk)
        (F.intervalMap (hij.trans hjk) hjk hij le_rfl)
        (F.intervalMap_comp_eq_zero hij hjk)) := by
  let p := F.intervalπ i j hij
  let r := F.chain.map (homOfLE hjk)
  let q := F.intervalπ j k hjk
  let x := F.intervalMap hij (hij.trans hjk) le_rfl hjk
  let y := F.intervalπ i k (hij.trans hjk)
  let sq : IsPushout p r x y := F.intervalSquare_isPushout hij hjk
  let m := pushoutQuotientMap p r q x y
    (F.interval_comp_π j k hjk) sq
  have hm : m = F.intervalMap (hij.trans hjk) hjk hij le_rfl := by
    let : Epi y :=
      (isAdmissibleEpi_g (intervalData F k i (hij.trans hjk)).exact).epi
    apply (cancel_epi y).1
    rw [show y ≫ m = q from
      pushoutQuotientMap_y p r q x y
        (F.interval_comp_π j k hjk) sq]
    dsimp only [q, y]
    have hid : F.chain.map (homOfLE (le_rfl : k ≤ k)) =
        𝟙 (F.chain.obj k) := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
    have hv := F.intervalπ_naturality
      (hij.trans hjk) hjk hij le_rfl
    rw [hid, Category.id_comp] at hv
    exact hv.symm
  have hExact := isAdmissibleExact_pushoutQuotientMap
    p r q x y (F.interval_comp_π j k hjk)
    (F.interval_exact j k hjk) sq
  simpa only [m, hm] using hExact

/-- The quotient-completed interval diagram of an admissible flag. -/
noncomputable def intervalDiagram : Ar n ⥤ C where
  obj A := F.intervalQuotient A.left A.right (leOfHom A.hom)
  map {A B} f := F.intervalMap (leOfHom A.hom) (leOfHom B.hom)
    (leOfHom f.left) (leOfHom f.right)
  map_id A := by
    let hij := leOfHom A.hom
    let : Epi (F.intervalπ A.left A.right hij) :=
      (isAdmissibleEpi_g (F.interval_exact A.left A.right hij)).epi
    apply (cancel_epi (F.intervalπ A.left A.right hij)).1
    rw [F.intervalπ_naturality hij hij le_rfl le_rfl]
    simp
  map_comp {A B D} f g := by
    let hA := leOfHom A.hom
    let hB := leOfHom B.hom
    let hD := leOfHom D.hom
    let hfL := leOfHom f.left
    let hfR := leOfHom f.right
    let hgL := leOfHom g.left
    let hgR := leOfHom g.right
    let : Epi (F.intervalπ A.left A.right hA) :=
      (isAdmissibleEpi_g (F.interval_exact A.left A.right hA)).epi
    apply (cancel_epi (F.intervalπ A.left A.right hA)).1
    rw [F.intervalπ_naturality hA hD
      (hfL.trans hgL) (hfR.trans hgR)]
    calc
      F.chain.map (homOfLE (hfR.trans hgR)) ≫
          F.intervalπ D.left D.right hD =
        (F.chain.map (homOfLE hfR) ≫
          F.chain.map (homOfLE hgR)) ≫
            F.intervalπ D.left D.right hD := by
              rw [← F.chain.map_comp]
              congr
      _ = F.chain.map (homOfLE hfR) ≫
          (F.chain.map (homOfLE hgR) ≫
            F.intervalπ D.left D.right hD) := Category.assoc _ _ _
      _ = F.chain.map (homOfLE hfR) ≫
          (F.intervalπ B.left B.right hB ≫
            F.intervalMap hB hD hgL hgR) := by
              rw [F.intervalπ_naturality hB hD hgL hgR]
      _ = (F.chain.map (homOfLE hfR) ≫
          F.intervalπ B.left B.right hB) ≫
            F.intervalMap hB hD hgL hgR :=
              (Category.assoc _ _ _).symm
      _ = (F.intervalπ A.left A.right hA ≫
          F.intervalMap hA hB hfL hfR) ≫
            F.intervalMap hB hD hgL hgR := by
              rw [F.intervalπ_naturality hA hB hfL hfR]
      _ = F.intervalπ A.left A.right hA ≫
          (F.intervalMap hA hB hfL hfR ≫
            F.intervalMap hB hD hgL hgR) := Category.assoc _ _ _

/-- The quotient of a repeated interval is zero. -/
theorem intervalQuotient_isZero (i : Fin (n + 1)) :
    IsZero (F.intervalQuotient i i le_rfl) := by
  let D := intervalData F i i le_rfl
  have hmap : F.chain.map (homOfLE (le_rfl : i ≤ i)) =
      𝟙 (F.chain.obj i) := by
    rw [Subsingleton.elim (homOfLE _) (𝟙 _), F.chain.map_id]
  let : Epi (F.chain.map (homOfLE (le_rfl : i ≤ i))) := by
    rw [hmap]
    infer_instance
  exact CokernelCofork.IsColimit.isZero_of_epi
    (isColimit_cokernelCofork_of_isAdmissibleExact D.exact)

/-- The quotient-completed finite Stage associated to an admissible flag. -/
noncomputable def toStage :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      Stage C n) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  refine ⟨F.intervalDiagram, ?_⟩
  refine { diag_isZero := ?_, cofiber_triple := ?_ }
  · intro i
    exact F.intervalQuotient_isZero i
  · intro i j k hij hjk
    change IsCofibrationSequence (C := C)
      (F.intervalMap hij (hij.trans hjk) le_rfl hjk)
      (F.intervalMap (hij.trans hjk) hjk hij le_rfl)
    exact ExactCategory.isCofibrationSequence_of_isAdmissibleExact
      (F.interval_triple_exact hij hjk)

/-- Cell computation for the quotient-completed Stage. -/
@[simp]
theorem toStage_obj_interval
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      F.toStage.obj.obj (interval i j hij) =
        F.intervalQuotient i j hij) :=
  rfl

/-- Horizontal Stage legs are the canonical quotient maps that enlarge the
right endpoint. -/
@[simp]
theorem toStage_map_horiz
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      F.toStage.obj.map (horiz hij hjk) =
        F.intervalMap hij (hij.trans hjk) le_rfl hjk) :=
  rfl

/-- Vertical Stage legs are the canonical quotient maps that enlarge the
left endpoint. -/
@[simp]
theorem toStage_map_vert
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      F.toStage.obj.map (vert hij hjk) =
        F.intervalMap (hij.trans hjk) hjk hij le_rfl) :=
  rfl

/-- The zero row of the completed Stage recovers the original filtration
object, with the canonical quotient projection as the forward map. -/
noncomputable def zeroRowIso (j : Fin (n + 1)) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      F.chain.obj j ≅ F.toStage.obj.obj
        (interval 0 j (Fin.zero_le j))) := by
  let D := intervalData F j 0 (Fin.zero_le j)
  have hIso : IsIso D.π :=
    isIso_g_of_isAdmissibleExact_of_isZero D.exact F.first_isZero
  exact @asIso C _ _ _ D.π hIso

/-- The zero-row comparison is represented by the interval quotient
projection. -/
@[simp]
theorem zeroRowIso_hom (j : Fin (n + 1)) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      (F.zeroRowIso j).hom = F.intervalπ 0 j (Fin.zero_le j)) :=
  rfl

end AdmissibleMonoFlag

end CategoryTheory.Waldhausen.SConstruction

end
