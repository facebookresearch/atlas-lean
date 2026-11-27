/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.ExactCategory.AdmissibleEpiKernelComposition
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridLift
public import MathlibExt.KTheory.Exact.Quillen.SpanFlag

/-!
# Span presentations and edgewise filtrations for Quillen simplices

A finite Quillen simplex admits adjacent raw-span representatives equipped
with exact six-cell flags.  From one such explicit presentation, this file
forms right-associated interval spans and the tail spans ending at the last
vertex.  Their pullback projections and the composite-kernel construction
give the literal admissible filtration

```text
0, K(n-1,n), ..., K(0,n), M(0,n), ..., M(n-1,n), X(n).
```

The construction deliberately retains the presentation as an input.  Only
its Prop-valued existence is public: there is no public representative
selector and no functorial choice of presentations.  This file constructs no
Stage completion, grid lift, fiber or contractibility result, bar
construction, realization, or Q/S comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenSimplexSpanFiltrationWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- Adjacent raw spans and exact flags presenting every generating arrow of
a finite Quillen simplex. -/
structure QuillenSimplexSpanPresentation {a : SimplexCategory}
    (q : QuillenQSimplex C a) where
  /-- Raw representative of the adjacent arrow `i ⟶ i+1`. -/
  span (i : Fin a.len) :
    QuillenSpan (q.obj' i.val (by omega)).obj
      (q.obj' (i.val + 1) (by omega)).obj
  /-- Exact six-cell flag on each adjacent representative. -/
  flag (i : Fin a.len) : QuillenSpanFlagData (span i)
  /-- Each representative has the prescribed adjacent quotient class. -/
  class_eq (i : Fin a.len) :
    QuillenQ.mkHom (span i) =
      q.map' i.val (i.val + 1) (by omega) (by omega)

namespace QuillenSimplexSpanPresentation

variable {a : SimplexCategory} {q : QuillenQSimplex C a}

/-- Every finite Quillen simplex has an adjacent flagged-span presentation.
This is only a proposition and exposes no chosen presentation. -/
theorem nonempty (q : QuillenQSimplex C a) :
    Nonempty (QuillenSimplexSpanPresentation q) := by
  classical
  have hSpan : ∀ i : Fin a.len,
      ∃ S : QuillenSpan (q.obj' i.val (by omega)).obj
          (q.obj' (i.val + 1) (by omega)).obj,
        QuillenQ.mkHom S =
          q.map' i.val (i.val + 1) (by omega) (by omega) := by
    intro i
    obtain ⟨S, hS⟩ := Quotient.exists_rep
      (q.map' i.val (i.val + 1) (by omega) (by omega))
    exact ⟨S, hS⟩
  choose span hClass using hSpan
  have hFlag : ∀ i : Fin a.len,
      Nonempty (QuillenSpanFlagData (span i)) :=
    fun i ↦ QuillenSpanFlagData.nonempty (span i)
  let flag := fun i ↦ (hFlag i).some
  exact ⟨{ span := span, flag := flag, class_eq := hClass }⟩

/-- Natural-index implementation of the right-associated interval span. -/
noncomputable def intervalSpanFromNat
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hkn : k ≤ a.len) (l : Fin (a.len + 1))
    (hkl : k ≤ l.val) :
    QuillenSpan (q.obj ⟨k, Nat.lt_succ_of_le hkn⟩).obj (q.obj l).obj := by
  by_cases hEq : k = l.val
  · have hl : l = ⟨k, Nat.lt_succ_of_le hkn⟩ := by ext; exact hEq.symm
    subst l
    exact Span.id (q.obj ⟨k, Nat.lt_succ_of_le hkn⟩).obj
  have hklt : k < a.len := by omega
  let i : Fin a.len := ⟨k, hklt⟩
  by_cases hAdj : k + 1 = l.val
  · have hl : l = i.succ := by ext; simpa [i] using hAdj.symm
    subst l
    have hkFin : (⟨k, Nat.lt_succ_of_le hkn⟩ : Fin (a.len + 1)) =
        i.castSucc := by ext; rfl
    rw [hkFin]
    exact P.span i
  · have hsucc : k + 1 ≤ l.val := by omega
    have hkFin : (⟨k, Nat.lt_succ_of_le hkn⟩ : Fin (a.len + 1)) =
        i.castSucc := by ext; rfl
    rw [hkFin]
    exact Span.comp (P.span i)
      (intervalSpanFromNat P (k + 1) (by omega) l hsucc)
termination_by a.len - k
decreasing_by omega

/-- Right-associated representative of an ordered interval.  Equal
endpoints give the identity span, adjacent endpoints give the stored span,
and a longer interval is the first adjacent span composed with the
right-associated remainder. -/
noncomputable def intervalSpan (P : QuillenSimplexSpanPresentation q)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenSpan (q.obj k).obj (q.obj l).obj :=
  intervalSpanFromNat P k.val (Nat.le_of_lt_succ k.isLt) l
    (Fin.le_iff_val_le_val.mp hkl)

@[simp]
theorem intervalSpan_refl (P : QuillenSimplexSpanPresentation q)
    (k : Fin (a.len + 1)) :
    P.intervalSpan k k le_rfl =
      (Span.id (q.obj k).obj : QuillenSpan (q.obj k).obj (q.obj k).obj) := by
  rw [intervalSpan, intervalSpanFromNat]
  split
  · rfl
  · contradiction

/-- An adjacent interval is represented by the stored adjacent span, without
an extra identity-span factor. -/
theorem intervalSpan_adjacent (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) :
    P.intervalSpan i.castSucc i.succ (Fin.castSucc_le_succ i) = P.span i := by
  rw [intervalSpan, intervalSpanFromNat]
  split
  · rename_i h
    change i.val = i.val + 1 at h
    omega
  · dsimp only
    split
    · rfl
    · rename_i h
      exact (h rfl).elim

/-- A nonadjacent interval has the fixed right-associated first-step
decomposition. -/
theorem intervalSpan_of_gap (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (l : Fin (a.len + 1))
    (hgap : i.val + 1 < l.val) :
    P.intervalSpan i.castSucc l (by
      rw [Fin.le_iff_val_le_val]
      simpa only [Fin.val_castSucc] using (show i.val ≤ l.val by omega)) =
      Span.comp (P.span i) (P.intervalSpan i.succ l (by
        rw [Fin.le_iff_val_le_val]
        simpa only [Fin.val_succ] using (show i.val + 1 ≤ l.val by omega))) := by
  rw [intervalSpan, intervalSpanFromNat]
  split
  · rename_i h
    change i.val = l.val at h
    omega
  · dsimp only
    split
    · rename_i h
      change i.val + 1 = l.val at h
      omega
    · rfl

/-- Class computation for the natural-index implementation. -/
theorem intervalSpanFromNat_mkHom
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hkn : k ≤ a.len) (l : Fin (a.len + 1))
    (hkl : k ≤ l.val) :
    QuillenQ.mkHom (intervalSpanFromNat P k hkn l hkl) =
      q.map' k l.val hkl (Nat.le_of_lt_succ l.isLt) := by
  by_cases hEq : k = l.val
  · subst k
    rw [show intervalSpanFromNat P l.val hkn l hkl =
        (Span.id (q.obj l).obj : QuillenSpan (q.obj l).obj (q.obj l).obj) by
      rw [intervalSpanFromNat]
      split
      · rfl
      · contradiction, AlgebraicKTheory.mkHom_id]
    exact (q.map'_self l.val (Nat.le_of_lt_succ l.isLt)).symm
  have hklt : k < a.len := by omega
  let i : Fin a.len := ⟨k, hklt⟩
  by_cases hAdj : k + 1 = l.val
  · have hl : l = i.succ := by ext; simpa [i] using hAdj.symm
    subst l
    rw [show intervalSpanFromNat P k hkn i.succ hkl = P.span i by
      rw [intervalSpanFromNat]
      split
      · contradiction
      · dsimp only
        split
        · rfl
        · contradiction]
    simpa only [i, ComposableArrows.map'] using P.class_eq i
  · have hsucc : k + 1 ≤ l.val := by omega
    rw [show intervalSpanFromNat P k hkn l hkl =
        Span.comp (P.span i)
          (intervalSpanFromNat P (k + 1) (by omega) l hsucc) by
      rw [intervalSpanFromNat]
      split
      · contradiction
      · dsimp only
        split
        · contradiction
        · rfl,
      ← AlgebraicKTheory.mkHom_comp, P.class_eq i,
      intervalSpanFromNat_mkHom P (k + 1) (by omega) l hsucc]
    exact (q.map'_comp k (k + 1) l.val (by omega) hsucc
      (Nat.le_of_lt_succ l.isLt)).symm
termination_by a.len - k
decreasing_by omega

/-- The right-associated interval span represents the corresponding map of
the Quillen simplex. -/
theorem intervalSpan_mkHom (P : QuillenSimplexSpanPresentation q)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenQ.mkHom (P.intervalSpan k l hkl) =
      q.map (homOfLE hkl) := by
  simpa only [intervalSpan, ComposableArrows.map'] using
    intervalSpanFromNat_mkHom P k.val (Nat.le_of_lt_succ k.isLt) l
      (Fin.le_iff_val_le_val.mp hkl)

/-- Tail span from vertex `k` to the last vertex, with the same fixed
right-associated bracketing. -/
noncomputable abbrev tailSpan (P : QuillenSimplexSpanPresentation q)
    (k : Fin (a.len + 1)) :
    QuillenSpan (q.obj k).obj (q.obj (Fin.last a.len)).obj :=
  P.intervalSpan k (Fin.last a.len) (Fin.le_last k)

@[simp]
theorem tailSpan_mkHom (P : QuillenSimplexSpanPresentation q)
    (k : Fin (a.len + 1)) :
    QuillenQ.mkHom (P.tailSpan k) =
      q.map (homOfLE (Fin.le_last k)) :=
  P.intervalSpan_mkHom k (Fin.last a.len) (Fin.le_last k)

/-- Natural-index form of the tail span, used to expose the recursive
pullback structure without dependent `Fin` transports. -/
noncomputable def tailSpanFromNat
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    QuillenSpan (q.obj' k (by omega)).obj
      (q.obj (Fin.last a.len)).obj := by
  let i : Fin a.len := ⟨k, hk⟩
  by_cases hlast : k + 1 = a.len
  · have hiLast : i.succ = Fin.last a.len := by ext; simpa [i] using hlast
    let eY : (q.obj i.succ).obj ≅ (q.obj (Fin.last a.len)).obj :=
      eqToIso (congrArg (fun j ↦ (q.obj j).obj) hiLast)
    exact
      { apex := (P.span i).apex
        l := (P.span i).l
        r := (P.span i).r ≫ eY.hom
        wl := (P.span i).wl
        wr := admissibleMono_comp.comp_mem _ _ (P.span i).wr
          (IsAdmissibleMono.of_isIso eY.hom) }
  · exact Span.comp (P.span i)
      (tailSpanFromNat P (k + 1) (by omega))
termination_by a.len - k
decreasing_by omega

/-- A nonfinal tail is the first adjacent span composed with the next tail,
with right-associated parentheses. -/
theorem tailSpanFromNat_step
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    tailSpanFromNat P k (by omega) =
      Span.comp (P.span ⟨k, by omega⟩)
        (tailSpanFromNat P (k + 1) (by omega)) := by
  rw [tailSpanFromNat]
  split
  · omega
  · rfl

/-- Kernel presentation already contained in an adjacent span flag. -/
noncomputable def adjacentKernelPresentation
    (P : QuillenSimplexSpanPresentation q) (i : Fin a.len) :
    AdmissibleEpiKernelPresentation (P.span i).l :=
  { kernel := (P.flag i).kernelObj
    ι := (P.flag i).kernelι
    zero := (P.flag i).kernel_left_zero
    exact := (P.flag i).kernel_apex_source_exact }

@[simp]
theorem adjacentKernelPresentation_kernel
    (P : QuillenSimplexSpanPresentation q) (i : Fin a.len) :
    (P.adjacentKernelPresentation i).kernel = (P.flag i).kernelObj :=
  rfl

@[simp]
theorem adjacentKernelPresentation_ι
    (P : QuillenSimplexSpanPresentation q) (i : Fin a.len) :
    (P.adjacentKernelPresentation i).ι = (P.flag i).kernelι :=
  rfl

/-- The actual pullback apex of a span composite, regarded as base-change
data for the next tail's left admissible epimorphism. -/
noncomputable def tailCompositeBaseChange
    {X Y Z : C} (S : QuillenSpan X Y) (T : QuillenSpan Y Z)
    (Qnext : AdmissibleEpiKernelPresentation T.l) :
    Qnext.BaseChange S.r := by
  let cone : PullbackCone S.r T.l :=
    PullbackCone.mk (Span.SpanBicat.πₗ S T)
      (Span.SpanBicat.πᵣ S T) (Span.SpanBicat.comp_comm S T)
  let hcone : IsLimit cone :=
    PullbackCone.IsLimit.mk (Span.SpanBicat.comp_comm S T)
      (fun x ↦ Span.SpanBicat.compLiftApex x.fst x.snd x.condition)
      (fun x ↦ by simp)
      (fun x ↦ by simp)
      (fun f g hf hg ↦ by
        apply Span.SpanBicat.comp_hom_ext_apex
        · rw [hf, Span.SpanBicat.compLiftApex_πₗ
            f.fst f.snd f.condition]
        · rw [hg, Span.SpanBicat.compLiftApex_πᵣ
            f.fst f.snd f.condition])
  let hpb : IsPullback (Span.SpanBicat.πₗ S T)
      (Span.SpanBicat.πᵣ S T) S.r T.l :=
    IsPullback.of_isLimit hcone
  exact
    { obj := (Span.comp S T).apex
      fst := Span.SpanBicat.πₗ S T
      snd := Span.SpanBicat.πᵣ S T
      square := hpb
      fst_admissible := by
        have hfst : (admissibleEpisOf C IsAdmissibleExact)
            (Span.SpanBicat.πₗ S T) :=
          MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
            (P := admissibleEpisOf C IsAdmissibleExact) hpb.flip T.wl
        change (admissibleEpisOf C IsAdmissibleExact)
          (Span.SpanBicat.πₗ S T)
        exact hfst }

/-- The composite span's left leg is the composite built from the actual
base-change projection. -/
theorem tailCompositeBaseChange_comp_l
    {X Y Z : C} (S : QuillenSpan X Y) (T : QuillenSpan Y Z)
    (Qnext : AdmissibleEpiKernelPresentation T.l) :
    (Span.comp S T).l =
      (tailCompositeBaseChange S T Qnext).fst ≫ S.l := by
  change (Span.comp S T).l = Span.SpanBicat.πₗ S T ≫ S.l
  exact Span.SpanBicat.comp_l S T

/-- Transport a kernel presentation across an isomorphism of the source
object, retaining the same kernel object. -/
noncomputable def transportKernelPresentationSource
    {A A' B : C} {p : A ⟶ B}
    (Q : AdmissibleEpiKernelPresentation p)
    (e : A ≅ A') (p' : A' ⟶ B) (he : e.hom ≫ p' = p) :
    AdmissibleEpiKernelPresentation p' := by
  have w : (Q.ι ≫ e.hom) ≫ p' = 0 := by
    rw [Category.assoc, he, Q.zero]
  let Sold : ShortComplex C := ShortComplex.mk Q.ι p Q.zero
  let Snew : ShortComplex C := ShortComplex.mk (Q.ι ≫ e.hom) p' w
  let eS : Sold ≅ Snew :=
    ShortComplex.isoMk (Iso.refl Q.kernel) e (Iso.refl B)
      (by simp [Sold, Snew]) (by simpa [Sold, Snew] using he)
  exact
    { kernel := Q.kernel
      ι := Q.ι ≫ e.hom
      zero := w
      exact := isAdmissibleExact_of_iso eS Q.exact }

@[simp]
theorem transportKernelPresentationSource_kernel
    {A A' B : C} {p : A ⟶ B}
    (Q : AdmissibleEpiKernelPresentation p)
    (e : A ≅ A') (p' : A' ⟶ B) (he : e.hom ≫ p' = p) :
    (transportKernelPresentationSource Q e p' he).kernel = Q.kernel :=
  rfl

/-- Compatible kernel presentation of a tail left leg.  At the last adjacent
tail this is the stored flag kernel.  Earlier tails use QGRID-A on the actual
pullback projection and the adjacent left leg, so successive kernel objects
come with the required admissible exact row. -/
noncomputable def tailKernelPresentationFromNat
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    AdmissibleEpiKernelPresentation
      (tailSpanFromNat P k hk).l := by
  by_cases hlast : k + 1 = a.len
  · let i : Fin a.len := ⟨k, hk⟩
    rw [tailSpanFromNat, dite_eq_left hlast]
    exact P.adjacentKernelPresentation i
  · have hstep : k + 1 < a.len := by omega
    let S := P.span ⟨k, by omega⟩
    let T := tailSpanFromNat P (k + 1) hstep
    let Qnext := tailKernelPresentationFromNat P (k + 1) hstep
    let R := tailCompositeBaseChange S T Qnext
    let Pproj := R.kernelPresentation
    let Qadj := P.adjacentKernelPresentation ⟨k, by omega⟩
    let U := Pproj.composite Qadj
    have hSpan : tailSpanFromNat P k hk = Span.comp S T :=
      P.tailSpanFromNat_step k hstep
    let spanIso : Span.comp S T ≅ tailSpanFromNat P k hk :=
      (eqToIso hSpan).symm
    let e : (Span.comp S T).apex ≅ (tailSpanFromNat P k hk).apex :=
      Span.SpanBicat.apexIso
        (X := ⟨(q.obj' k (by omega)).obj⟩)
        (Y := ⟨(q.obj (Fin.last a.len)).obj⟩) spanIso
    have he : e.hom ≫ (tailSpanFromNat P k hk).l =
        R.fst ≫ S.l :=
      spanIso.hom.hom_l.trans (tailCompositeBaseChange_comp_l S T Qnext)
    exact transportKernelPresentationSource U e
      (tailSpanFromNat P k hk).l he
termination_by a.len - k
decreasing_by omega

/-- Kernel presentation of the tail from a nonfinal vertex. -/
noncomputable def tailKernelPresentation
    (P : QuillenSimplexSpanPresentation q) (k : Fin a.len) :
    AdmissibleEpiKernelPresentation (tailSpanFromNat P k.val k.isLt).l :=
  tailKernelPresentationFromNat P k.val k.isLt

/-- Successor map in the kernel half of the tail filtration. -/
noncomputable def tailKernelSuccFromNat
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    (tailKernelPresentationFromNat P (k + 1) hk).kernel ⟶
      (tailKernelPresentationFromNat P k (by omega)).kernel := by
  let S := P.span ⟨k, by omega⟩
  let T := tailSpanFromNat P (k + 1) hk
  let Qnext := tailKernelPresentationFromNat P (k + 1) hk
  let R := tailCompositeBaseChange S T Qnext
  let Pproj := R.kernelPresentation
  let Qadj := P.adjacentKernelPresentation ⟨k, by omega⟩
  let f : Pproj.kernel ⟶ (Pproj.composite Qadj).kernel :=
    (Pproj.compositeKernelSequence Qadj).f
  have hSource : Qnext.kernel = Pproj.kernel :=
    R.kernelPresentation_kernel.symm
  have hTarget :
      (tailKernelPresentationFromNat P k (by omega)).kernel =
        (Pproj.composite Qadj).kernel := by
    rw [tailKernelPresentationFromNat]
    split
    · omega
    · apply eq_of_heq
      rfl
  exact eqToHom hSource ≫ f ≫ eqToHom hTarget.symm

/-- Kernel-tower successor maps are admissible monomorphisms. -/
theorem tailKernelSuccFromNat_admissible
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    IsAdmissibleMono (P.tailKernelSuccFromNat k hk) := by
  let S := P.span ⟨k, by omega⟩
  let T := tailSpanFromNat P (k + 1) hk
  let Qnext := tailKernelPresentationFromNat P (k + 1) hk
  let R := tailCompositeBaseChange S T Qnext
  let Pproj := R.kernelPresentation
  let Qadj := P.adjacentKernelPresentation ⟨k, by omega⟩
  let f : Pproj.kernel ⟶ (Pproj.composite Qadj).kernel :=
    (Pproj.compositeKernelSequence Qadj).f
  have hf : IsAdmissibleMono f :=
    isAdmissibleMono_f (Pproj.compositeKernelSequence_exact Qadj)
  have hSource : Qnext.kernel = Pproj.kernel :=
    R.kernelPresentation_kernel.symm
  have hTarget :
      (tailKernelPresentationFromNat P k (by omega)).kernel =
        (Pproj.composite Qadj).kernel := by
    rw [tailKernelPresentationFromNat]
    split
    · omega
    · apply eq_of_heq
      rfl
  let g : (Pproj.composite Qadj).kernel ⟶
      (tailKernelPresentationFromNat P k (by omega)).kernel :=
    eqToHom hTarget.symm
  change IsAdmissibleMono (eqToHom hSource ≫ f ≫ g)
  have hRight : IsAdmissibleMono (f ≫ g) :=
    admissibleMono_comp.comp_mem _ _ hf (IsAdmissibleMono.of_isIso g)
  exact admissibleMono_comp.comp_mem _ _
    (IsAdmissibleMono.of_isIso (eqToHom hSource)) hRight

/-- Successor map between consecutive tail apices.  It is the right
projection of the pullback defining span composition. -/
noncomputable def tailApexSuccFromNat
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    (tailSpanFromNat P k (by omega)).apex ⟶
      (tailSpanFromNat P (k + 1) hk).apex := by
  let S := P.span ⟨k, by omega⟩
  let T := tailSpanFromNat P (k + 1) hk
  let Qnext := tailKernelPresentationFromNat P (k + 1) hk
  let R := tailCompositeBaseChange S T Qnext
  have hSpan : tailSpanFromNat P k (by omega) = Span.comp S T :=
    P.tailSpanFromNat_step k hk
  exact eqToHom (congrArg Span.apex hSpan) ≫ R.snd

/-- Tail-apex successor maps are admissible monomorphisms. -/
theorem tailApexSuccFromNat_admissible
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    IsAdmissibleMono (P.tailApexSuccFromNat k hk) := by
  let S := P.span ⟨k, by omega⟩
  let T := tailSpanFromNat P (k + 1) hk
  let Qnext := tailKernelPresentationFromNat P (k + 1) hk
  let R := tailCompositeBaseChange S T Qnext
  have hR : IsAdmissibleMono R.snd :=
    isAdmissibleMono_of_isPullback R.square S.wr Qnext.epi_admissible
  unfold tailApexSuccFromNat
  exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso _) hR

/-- Object on the straight/right half of the filtration.  Before the last
vertex it is a tail apex; at the last vertex it is the terminal simplex
object itself. -/
noncomputable def rightTailObject
    (P : QuillenSimplexSpanPresentation q)
    (k : Fin (a.len + 1)) : C :=
  if hk : k.val < a.len then
    (tailSpanFromNat P k.val hk).apex
  else
    (q.obj (Fin.last a.len)).obj

@[simp]
theorem rightTailObject_last
    (P : QuillenSimplexSpanPresentation q) :
    P.rightTailObject (Fin.last a.len) = (q.obj (Fin.last a.len)).obj := by
  rw [rightTailObject, dite_eq_right]
  simp

theorem rightTailObject_of_lt
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    P.rightTailObject ⟨k, by omega⟩ = (tailSpanFromNat P k hk).apex := by
  rw [rightTailObject, dite_eq_left hk]

/-- Successor map on the straight/right half, including the final adjacent
span's right leg into the last simplex object. -/
noncomputable def rightTailSuccFromNat
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    P.rightTailObject ⟨k, by omega⟩ ⟶
      P.rightTailObject ⟨k + 1, by omega⟩ := by
  have hSource := P.rightTailObject_of_lt k hk
  by_cases hstep : k + 1 < a.len
  · have hTarget := P.rightTailObject_of_lt (k + 1) hstep
    exact eqToHom hSource ≫ P.tailApexSuccFromNat k hstep ≫
      eqToHom hTarget.symm
  · have hlast : k + 1 = a.len := by omega
    have hTarget : P.rightTailObject ⟨k + 1, by omega⟩ =
        (q.obj (Fin.last a.len)).obj := by
      rw [rightTailObject, dite_eq_right hstep]
    exact eqToHom hSource ≫ (tailSpanFromNat P k hk).r ≫
      eqToHom hTarget.symm

/-- Every successor on the straight/right half is an admissible mono. -/
theorem rightTailSuccFromNat_admissible
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    IsAdmissibleMono (P.rightTailSuccFromNat k hk) := by
  have hSource := P.rightTailObject_of_lt k hk
  by_cases hstep : k + 1 < a.len
  · have hTarget := P.rightTailObject_of_lt (k + 1) hstep
    let f := P.tailApexSuccFromNat k hstep
    have hf := P.tailApexSuccFromNat_admissible k hstep
    unfold rightTailSuccFromNat
    rw [dite_eq_left hstep]
    change IsAdmissibleMono (eqToHom hSource ≫ f ≫ eqToHom hTarget.symm)
    have hRight : IsAdmissibleMono (f ≫ eqToHom hTarget.symm) :=
      admissibleMono_comp.comp_mem _ _ hf (IsAdmissibleMono.of_isIso _)
    exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso _) hRight
  · have hTarget : P.rightTailObject ⟨k + 1, by omega⟩ =
        (q.obj (Fin.last a.len)).obj := by
      rw [rightTailObject, dite_eq_right hstep]
    let f := (tailSpanFromNat P k hk).r
    have hf : IsAdmissibleMono f := (tailSpanFromNat P k hk).wr
    unfold rightTailSuccFromNat
    rw [dite_eq_right hstep]
    change IsAdmissibleMono (eqToHom hSource ≫ f ≫ eqToHom hTarget.symm)
    have hRight : IsAdmissibleMono (f ≫ eqToHom hTarget.symm) :=
      admissibleMono_comp.comp_mem _ _ hf (IsAdmissibleMono.of_isIso _)
    exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso _) hRight

/-- Object function of the full literal edgewise filtration. -/
noncomputable def filtrationObject
    (P : QuillenSimplexSpanPresentation q)
    (j : Fin ((edgewiseQ.obj a).len + 1)) : C := by
  have hj : j.val < 2 * a.len + 2 := by
    simpa only [edgewiseQ_obj_len] using j.isLt
  by_cases hzero : j.val = 0
  · exact 0
  by_cases hleft : j.val ≤ a.len
  · exact (tailKernelPresentationFromNat P (a.len - j.val) (by omega)).kernel
  · let k : Fin (a.len + 1) := ⟨j.val - (a.len + 1), by omega⟩
    exact P.rightTailObject k

@[simp]
theorem filtrationObject_zero
    (P : QuillenSimplexSpanPresentation q) :
    P.filtrationObject ⟨0, by simp⟩ = (0 : C) := by
  rw [filtrationObject]
  simp

/-- Formula at every nonterminal reversed/left edgewise index. -/
theorem filtrationObject_left
    (P : QuillenSimplexSpanPresentation q) (k : Fin a.len) :
    P.filtrationObject (edgewiseLeftIndex a k.castSucc) =
      (P.tailKernelPresentation k).kernel := by
  have hzero : a.len - k.val ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt k.isLt)
  have hleft : a.len - k.val ≤ a.len := Nat.sub_le _ _
  rw [show edgewiseLeftIndex a k.castSucc =
      (⟨a.len - k.val, by simp only [edgewiseQ_obj_len]; omega⟩ :
        Fin ((edgewiseQ.obj a).len + 1)) by ext; simp]
  rw [filtrationObject]
  simp only [dite_eq_right hzero, dite_eq_left hleft]
  let k' : Fin a.len := ⟨a.len - (a.len - k.val), by
    rw [Nat.sub_sub_self (Nat.le_of_lt k.isLt)]
    exact k.isLt⟩
  change (P.tailKernelPresentation k').kernel =
    (P.tailKernelPresentation k).kernel
  have hk' : k' = k := by
    apply Fin.ext
    exact Nat.sub_sub_self (Nat.le_of_lt k.isLt)
  exact congrArg (fun r : Fin a.len ↦
    (P.tailKernelPresentation r).kernel) hk'

/-- Formula at the terminal reversed/left edgewise index. -/
theorem filtrationObject_left_last
    (P : QuillenSimplexSpanPresentation q) :
    P.filtrationObject (edgewiseLeftIndex a (Fin.last a.len)) = (0 : C) := by
  rw [show edgewiseLeftIndex a (Fin.last a.len) =
      (⟨0, by simp⟩ :
        Fin ((edgewiseQ.obj a).len + 1)) by ext; simp]
  exact P.filtrationObject_zero

/-- Formula at every straight/right edgewise index. -/
theorem filtrationObject_right
    (P : QuillenSimplexSpanPresentation q)
    (k : Fin (a.len + 1)) :
    P.filtrationObject (edgewiseRightIndex a k) = P.rightTailObject k := by
  unfold filtrationObject
  simp only [edgewiseRightIndex_val]
  split
  · omega
  · split
    · omega
    · congr 2; omega

/-- Transporting both endpoints of an admissible mono along equality
isomorphisms preserves admissibility. -/
theorem isAdmissibleMono_eqToHom_comp_comp_eqToHom
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    (f : X' ⟶ Y') (hf : IsAdmissibleMono f) :
    IsAdmissibleMono (eqToHom hX ≫ f ≫ eqToHom hY.symm) := by
  have hRight : IsAdmissibleMono (f ≫ eqToHom hY.symm) :=
    admissibleMono_comp.comp_mem _ _ hf (IsAdmissibleMono.of_isIso _)
  exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso _) hRight

/-- One successor arrow of the literal filtration, bundled with its
admissibility proof. -/
structure QuillenSimplexFiltrationStep
    (P : QuillenSimplexSpanPresentation q)
    (j : Fin (edgewiseQ.obj a).len) where
  hom : P.filtrationObject j.castSucc ⟶ P.filtrationObject j.succ
  admissible : IsAdmissibleMono hom

/-- Successor arrows of the full filtration in literal edgewise order. -/
noncomputable def filtrationStep
    (P : QuillenSimplexSpanPresentation q)
    (j : Fin (edgewiseQ.obj a).len) :
    QuillenSimplexFiltrationStep P j := by
  have hjBound : j.val < 2 * a.len + 1 := by
    simpa only [edgewiseQ_obj_len] using j.isLt
  by_cases hzero : j.val = 0
  · have hIndex : j.castSucc =
        (⟨0, by simp⟩ : Fin ((edgewiseQ.obj a).len + 1)) := by
      apply Fin.ext
      simpa using hzero
    have hSource : P.filtrationObject j.castSucc = (0 : C) :=
      (congrArg P.filtrationObject hIndex).trans P.filtrationObject_zero
    let f : (0 : C) ⟶ P.filtrationObject j.succ := 0
    exact
      { hom := eqToHom hSource ≫ f
        admissible := admissibleMono_comp.comp_mem _ _
          (IsAdmissibleMono.of_isIso _) (IsAdmissibleMono.fromZero f) }
  by_cases hkernel : j.val < a.len
  · let kt : Fin a.len := ⟨a.len - (j.val + 1), by omega⟩
    let ks : Fin a.len := ⟨a.len - j.val, by omega⟩
    have hkt : kt.val + 1 < a.len := by
      dsimp only [kt]
      omega
    let kts : Fin a.len := ⟨kt.val + 1, hkt⟩
    have hks : ks = kts := by
      apply Fin.ext
      dsimp only [ks, kts, kt]
      omega
    have hSourceIndex : j.castSucc = edgewiseLeftIndex a ks.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc, edgewiseLeftIndex_val]
      exact (Nat.sub_sub_self (Nat.le_of_lt hkernel)).symm
    have hTargetIndex : j.succ = edgewiseLeftIndex a kt.castSucc := by
      apply Fin.ext
      simp only [Fin.val_succ, edgewiseLeftIndex_val]
      exact (Nat.sub_sub_self (Nat.succ_le_of_lt hkernel)).symm
    have hSource : P.filtrationObject j.castSucc =
        (tailKernelPresentationFromNat P (kt.val + 1) hkt).kernel :=
      (congrArg P.filtrationObject hSourceIndex).trans
        ((P.filtrationObject_left ks).trans
          (congrArg (fun r : Fin a.len ↦
            (P.tailKernelPresentation r).kernel) hks))
    have hTarget : P.filtrationObject j.succ =
        (tailKernelPresentationFromNat P kt.val (by omega)).kernel :=
      (congrArg P.filtrationObject hTargetIndex).trans
        (P.filtrationObject_left kt)
    let f := P.tailKernelSuccFromNat kt.val hkt
    exact
      { hom := eqToHom hSource ≫ f ≫ eqToHom hTarget.symm
        admissible := isAdmissibleMono_eqToHom_comp_comp_eqToHom
          hSource hTarget f (P.tailKernelSuccFromNat_admissible kt.val hkt) }
  by_cases hbridge : j.val = a.len
  · have hn : 0 < a.len := by omega
    let k0 : Fin a.len := ⟨0, hn⟩
    have hSourceIndex : j.castSucc = edgewiseLeftIndex a k0.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc, edgewiseLeftIndex_val]
      dsimp only [k0]
      omega
    have hTargetIndex : j.succ =
        edgewiseRightIndex a (0 : Fin (a.len + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, edgewiseRightIndex_val, Fin.val_zero]
      omega
    have hSource : P.filtrationObject j.castSucc =
        (P.tailKernelPresentation k0).kernel :=
      (congrArg P.filtrationObject hSourceIndex).trans
        (P.filtrationObject_left k0)
    have hTarget : P.filtrationObject j.succ =
        (tailSpanFromNat P 0 hn).apex :=
      (congrArg P.filtrationObject hTargetIndex).trans
        ((P.filtrationObject_right (0 : Fin (a.len + 1))).trans
          (P.rightTailObject_of_lt 0 hn))
    let f := (P.tailKernelPresentation k0).ι
    exact
      { hom := eqToHom hSource ≫ f ≫ eqToHom hTarget.symm
        admissible := isAdmissibleMono_eqToHom_comp_comp_eqToHom
          hSource hTarget f (P.tailKernelPresentation k0).ι_admissible }
  · have hright : a.len < j.val := by omega
    let kv := j.val - (a.len + 1)
    have hk : kv < a.len := by dsimp only [kv]; omega
    let k0 : Fin (a.len + 1) := ⟨kv, by omega⟩
    let k1 : Fin (a.len + 1) := ⟨kv + 1, by omega⟩
    have hSourceIndex : j.castSucc = edgewiseRightIndex a k0 := by
      apply Fin.ext
      simp only [Fin.val_castSucc, edgewiseRightIndex_val]
      dsimp only [k0, kv]
      omega
    have hTargetIndex : j.succ = edgewiseRightIndex a k1 := by
      apply Fin.ext
      simp only [Fin.val_succ, edgewiseRightIndex_val]
      dsimp only [k1, kv]
      omega
    have hSource : P.filtrationObject j.castSucc = P.rightTailObject k0 :=
      (congrArg P.filtrationObject hSourceIndex).trans
        (P.filtrationObject_right k0)
    have hTarget : P.filtrationObject j.succ = P.rightTailObject k1 :=
      (congrArg P.filtrationObject hTargetIndex).trans
        (P.filtrationObject_right k1)
    let f := P.rightTailSuccFromNat kv hk
    exact
      { hom := eqToHom hSource ≫ f ≫ eqToHom hTarget.symm
        admissible := isAdmissibleMono_eqToHom_comp_comp_eqToHom
          hSource hTarget f (P.rightTailSuccFromNat_admissible kv hk) }

/-- The full zero-row filtration, retaining its first-zero and admissible
successor properties. -/
structure QuillenSimplexSpanFiltration
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (m : ℕ) where
  chain : ComposableArrows C m
  first_isZero : IsZero (chain.obj 0)
  step_admissible : ∀ i : Fin m,
    IsAdmissibleMono (chain.map' i.val (i.val + 1) (by omega) (by omega))

/-- Literal edgewise kernel/apex filtration attached to one explicit simplex
presentation. -/
noncomputable def filtration
    (P : QuillenSimplexSpanPresentation q) :
    QuillenSimplexSpanFiltration C (edgewiseQ.obj a).len := by
  let chain := ComposableArrows.mkOfObjOfMapSucc P.filtrationObject
    (fun j ↦ (P.filtrationStep j).hom)
  exact
    { chain := chain
      first_isZero := by
        change IsZero (P.filtrationObject 0)
        rw [show (0 : Fin ((edgewiseQ.obj a).len + 1)) =
          ⟨0, by simp⟩ by rfl, P.filtrationObject_zero]
        exact isZero_zero C
      step_admissible := by
        intro i
        rw [show chain.map' i.val (i.val + 1) (by omega) (by omega) =
            (P.filtrationStep i).hom by
          exact ComposableArrows.mkOfObjOfMapSucc_map_succ
            P.filtrationObject (fun j ↦ (P.filtrationStep j).hom)
              i.val i.isLt]
        exact (P.filtrationStep i).admissible }

@[simp]
theorem filtration_chain_obj
    (P : QuillenSimplexSpanPresentation q)
    (j : Fin ((edgewiseQ.obj a).len + 1)) :
    P.filtration.chain.obj j = P.filtrationObject j :=
  rfl

theorem filtration_chain_map_succ
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin (edgewiseQ.obj a).len) :
    P.filtration.chain.map' i.val (i.val + 1) (by omega) (by omega) =
      (P.filtrationStep i).hom :=
  ComposableArrows.mkOfObjOfMapSucc_map_succ
    P.filtrationObject (fun j ↦ (P.filtrationStep j).hom) i.val i.isLt

/-- Left-index object formula on the packaged filtration. -/
theorem filtration_chain_obj_left
    (P : QuillenSimplexSpanPresentation q) (k : Fin a.len) :
    P.filtration.chain.obj (edgewiseLeftIndex a k.castSucc) =
      (P.tailKernelPresentation k).kernel :=
  P.filtrationObject_left k

/-- Terminal left index is the chosen zero object. -/
theorem filtration_chain_obj_left_last
    (P : QuillenSimplexSpanPresentation q) :
    P.filtration.chain.obj (edgewiseLeftIndex a (Fin.last a.len)) = (0 : C) :=
  P.filtrationObject_left_last

/-- Right-index object formula on the packaged filtration. -/
theorem filtration_chain_obj_right
    (P : QuillenSimplexSpanPresentation q)
    (k : Fin (a.len + 1)) :
    P.filtration.chain.obj (edgewiseRightIndex a k) =
      P.rightTailObject k :=
  P.filtrationObject_right k

end QuillenSimplexSpanPresentation

end AlgebraicKTheory

end
