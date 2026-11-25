/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.OriginalPushoutRootPresentation
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.CompactRootUnderPresentability

/-!
# Finite idempotent capture in one original Under presentation

Capture the actual root-compatible generator-target map through the whole
original rooted cocone. One genuine eventual-equality refinement forces
local idempotence. The data retains the initial index, initial captured
map, final index and actual refinement arrow of the same original J.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uJ vJ u v

namespace CategoryTheory.SmallObject.CompactRootIdempotentCapture

open Limits OriginalPushoutRootPresentation

section UnderPresentability

variable {C : Type u} [Category.{v} C] {D E : C}
  (f : D ⟶ E) (chi : Cardinal.{w}) [Fact chi.IsRegular]
  [HasCardinalFilteredColimits C chi]
  [IsCardinalPresentable D chi] [IsCardinalPresentable E chi]

/-- Compactness of the original two ends gives the actual rooted source its same rank. -/
theorem underSourcePresentable : IsCardinalPresentable (Under.mk f) chi := by
  let : (Functor.fromPUnit.{0} D).PreservesCardinalPresentable chi :=
    CompactRootUnderPresentability.rootFunctorPresentable D chi
  exact Comma.isCardinalPresentable_mk
    (F₁ := Functor.fromPUnit.{0} D) (F₂ := 𝟭 C) (κ := chi)
    (X₁ := Discrete.mk PUnit.unit) (X₂ := E) f

end UnderPresentability

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {D X E : C} (u : D ⟶ X) (f : D ⟶ E)
  {J : Type uJ} [Category.{vJ} J] (p : ColimitPresentation J (Under.mk u))

/-- The local endomorphism uses the same original native root and captured cell map. -/
def localEndomorphism (j : J) (z : E ⟶ stage u f p j)
    (hz : f ≫ z = (p.diag.obj j).hom ≫ root u f p j) :
    stage u f p j ⟶ stage u f p j :=
  pushout.desc (root u f p j) z hz.symm

/-- The actual local root is fixed by its selected descender. -/
theorem localEndomorphism_root (j : J) (z : E ⟶ stage u f p j)
    (hz : f ≫ z = (p.diag.obj j).hom ≫ root u f p j) :
    root u f p j ≫ localEndomorphism u f p j z hz = root u f p j :=
  pushout.inl_desc _ _ _

/-- The actual local generator-target inclusion recovers the captured map. -/
theorem localEndomorphism_local (j : J) (z : E ⟶ stage u f p j)
    (hz : f ≫ z = (p.diag.obj j).hom ≫ root u f p j) :
    cellLeg u f p j ≫ localEndomorphism u f p j z hz = z :=
  pushout.inr_desc _ _ _

/-- The same original refinement map preserves the full root equation. -/
theorem refinementRoot {j k : J} (h : j ⟶ k) (z : E ⟶ stage u f p j)
    (hz : f ≫ z = (p.diag.obj j).hom ≫ root u f p j) :
    f ≫ (z ≫ transition u f p h) = (p.diag.obj k).hom ≫ root u f p k := by
  calc
    _ = (f ≫ z) ≫ transition u f p h := (Category.assoc _ _ _).symm
    _ = ((p.diag.obj j).hom ≫ root u f p j) ≫ transition u f p h := by rw [hz]
    _ = (p.diag.obj j).hom ≫ ((p.diag.map h).right ≫ root u f p k) := by
      rw [Category.assoc, root_transition]
    _ = ((p.diag.obj j).hom ≫ (p.diag.map h).right) ≫ root u f p k :=
      (Category.assoc _ _ _).symm
    _ = _ := by rw [Under.w]

/-- Both original coefficient inclusions derive the local refinement square. -/
theorem refinementSquare {j k : J} (h : j ⟶ k) (z : E ⟶ stage u f p j)
    (hz : f ≫ z = (p.diag.obj j).hom ≫ root u f p j) :
    localEndomorphism u f p j z hz ≫ transition u f p h =
      transition u f p h ≫ localEndomorphism u f p k (z ≫ transition u f p h)
        (refinementRoot u f p h z hz) := by
  apply pushout.hom_ext
  · calc
      _ = (root u f p j ≫ localEndomorphism u f p j z hz) ≫ transition u f p h :=
        (Category.assoc _ _ _).symm
      _ = root u f p j ≫ transition u f p h := by rw [localEndomorphism_root]
      _ = (p.diag.map h).right ≫ root u f p k := root_transition u f p h
      _ = (p.diag.map h).right ≫
          (root u f p k ≫ localEndomorphism u f p k (z ≫ transition u f p h)
            (refinementRoot u f p h z hz)) := by rw [localEndomorphism_root]
      _ = _ := by rw [← Category.assoc, ← root_transition, Category.assoc]
  · calc
      _ = (cellLeg u f p j ≫ localEndomorphism u f p j z hz) ≫ transition u f p h :=
        (Category.assoc _ _ _).symm
      _ = z ≫ transition u f p h := by rw [localEndomorphism_local]
      _ = cellLeg u f p k ≫ localEndomorphism u f p k (z ≫ transition u f p h)
          (refinementRoot u f p h z hz) := (localEndomorphism_local _ _ _ _ _ _).symm
      _ = _ := by rw [← local_transition u f p h, Category.assoc]

/-- The complete initial rooted capture, retaining its actual root equation. -/
abbrev RootCapture : Type _ :=
  Σ j : J, {z : E ⟶ stage u f p j //
    f ≫ z = (p.diag.obj j).hom ≫ root u f p j}

/-- The original initial capture and the actual chosen refinement in the SAME J. -/
abbrev Trace : Type _ :=
  Σ b : RootCapture u f p, Σ k : J, b.1 ⟶ k

/-- The literal first index of the same original presentation. -/
abbrev initialIndex (t : Trace u f p) : J := t.1.1

/-- The actual original first captured generator-target map. -/
abbrev initialCell (t : Trace u f p) : E ⟶ stage u f p (initialIndex u f p t) := t.1.2.1

/-- Its whole original fixed-root equality. -/
theorem initialRootEquation (t : Trace u f p) :
    f ≫ initialCell u f p t =
      (p.diag.obj (initialIndex u f p t)).hom ≫ root u f p (initialIndex u f p t) :=
  t.1.2.2

/-- The actual final index selected by eventual equality. -/
abbrev index (t : Trace u f p) : J := t.2.1

/-- The same original refinement arrow, with its original source and target. -/
abbrev refinement (t : Trace u f p) : initialIndex u f p t ⟶ index u f p t := t.2.2

/-- The original first local descender, before the equality refinement. -/
def initialEndomorphism (t : Trace u f p) :
    stage u f p (initialIndex u f p t) ⟶ stage u f p (initialIndex u f p t) :=
  localEndomorphism u f p (initialIndex u f p t) (initialCell u f p t)
    (initialRootEquation u f p t)

/-- The actual final captured cell map is transported through that SAME refinement. -/
def refinedCell (t : Trace u f p) : E ⟶ stage u f p (index u f p t) :=
  initialCell u f p t ≫ transition u f p (refinement u f p t)

/-- The final root equation uses the original root maps, without a replacement. -/
theorem refinedRootEquation (t : Trace u f p) :
    f ≫ refinedCell u f p t =
      (p.diag.obj (index u f p t)).hom ≫ root u f p (index u f p t) :=
  refinementRoot u f p (refinement u f p t) (initialCell u f p t)
    (initialRootEquation u f p t)

/-- The final local endomorphism is the native descender of those actual selected fields. -/
def endomorphism (t : Trace u f p) :
    stage u f p (index u f p t) ⟶ stage u f p (index u f p t) :=
  localEndomorphism u f p (index u f p t) (refinedCell u f p t)
    (refinedRootEquation u f p t)

/-- This naturality square is derived from the same two original coefficient inclusions. -/
theorem traceSquare (t : Trace u f p) :
    initialEndomorphism u f p t ≫ transition u f p (refinement u f p t) =
      transition u f p (refinement u f p t) ≫ endomorphism u f p t :=
  refinementSquare u f p (refinement u f p t) (initialCell u f p t)
    (initialRootEquation u f p t)

/-- Only actual capture and actual delayed equality are stored as proof certificates. -/
def Valid (e : pushout u f ⟶ pushout u f) (t : Trace u f p) : Prop :=
  initialCell u f p t ≫
      CompactRootPushoutPresentation.comparison u f p (initialIndex u f p t) =
        pushout.inr u f ≫ e ∧
    (initialCell u f p t ≫ initialEndomorphism u f p t) ≫
      transition u f p (refinement u f p t) = refinedCell u f p t

/-- A standard subtype retains the actual trace and its two proof certificates. -/
abbrev Data (e : pushout u f ⟶ pushout u f) : Type _ :=
  {t : Trace u f p // Valid u f p e t}

/-- The delayed equality and derived refinement square force the final cell map to be fixed. -/
theorem refinedCell_endomorphism (e : pushout u f ⟶ pushout u f) (d : Data u f p e) :
    refinedCell u f p d.1 ≫ endomorphism u f p d.1 = refinedCell u f p d.1 := by
  change (initialCell u f p d.1 ≫ transition u f p (refinement u f p d.1)) ≫
      endomorphism u f p d.1 = refinedCell u f p d.1
  rw [Category.assoc, ← traceSquare, ← Category.assoc]
  exact d.2.2

/-- The actual selected local root is fixed by construction. -/
theorem endomorphism_root (e : pushout u f ⟶ pushout u f) (d : Data u f p e) :
    root u f p (index u f p d.1) ≫ endomorphism u f p d.1 =
      root u f p (index u f p d.1) :=
  localEndomorphism_root _ _ _ _ _ _

/-- The actual final cell inclusion recovers its same selected captured map. -/
theorem endomorphism_local (e : pushout u f ⟶ pushout u f) (d : Data u f p e) :
    cellLeg u f p (index u f p d.1) ≫ endomorphism u f p d.1 = refinedCell u f p d.1 :=
  localEndomorphism_local _ _ _ _ _ _

/-- Actual delayed equality proves local idempotence by the original native pushout UP. -/
theorem endomorphism_idempotent (e : pushout u f ⟶ pushout u f) (d : Data u f p e) :
    endomorphism u f p d.1 ≫ endomorphism u f p d.1 = endomorphism u f p d.1 := by
  apply pushout.hom_ext
  · rw [← Category.assoc, endomorphism_root]
    exact endomorphism_root u f p e d
  · change cellLeg u f p (index u f p d.1) ≫
      (endomorphism u f p d.1 ≫ endomorphism u f p d.1) =
        cellLeg u f p (index u f p d.1) ≫ endomorphism u f p d.1
    rw [← Category.assoc, endomorphism_local]
    exact refinedCell_endomorphism u f p e d

section Connected

variable [IsConnected J]

omit [IsConnected J] in
/-- A root-compatible captured map intertwines the actual local and global endomorphisms. -/
theorem localIntertwines (e : pushout u f ⟶ pushout u f)
    (fixRoot : pushout.inl u f ≫ e = pushout.inl u f)
    (j : J) (z : E ⟶ stage u f p j)
    (hz : f ≫ z = (p.diag.obj j).hom ≫ root u f p j)
    (hFactor : z ≫ CompactRootPushoutPresentation.comparison u f p j = pushout.inr u f ≫ e) :
    localEndomorphism u f p j z hz ≫ CompactRootPushoutPresentation.comparison u f p j =
      CompactRootPushoutPresentation.comparison u f p j ≫ e := by
  apply pushout.hom_ext
  · rw [← Category.assoc, localEndomorphism_root, ← Category.assoc,
      CompactRootPushoutPresentation.comparison_root, Category.assoc, fixRoot]
  · rw [← Category.assoc, localEndomorphism_local, hFactor, ← Category.assoc,
      CompactRootPushoutPresentation.comparison_local]

/-- The final original cofan factor is derived through the literal original refinement. -/
theorem refinedFactor (e : pushout u f ⟶ pushout u f) (d : Data u f p e) :
    refinedCell u f p d.1 ≫
      CompactRootPushoutPresentation.comparison u f p (index u f p d.1) =
        pushout.inr u f ≫ e := by
  rw [refinedCell, Category.assoc, transition_comparison]
  exact d.2.1

/-- The final selected endomorphism retains the original endpoint comparison function. -/
theorem endomorphism_intertwines (e : pushout u f ⟶ pushout u f)
    (fixRoot : pushout.inl u f ≫ e = pushout.inl u f) (d : Data u f p e) :
    endomorphism u f p d.1 ≫
      CompactRootPushoutPresentation.comparison u f p (index u f p d.1) =
        CompactRootPushoutPresentation.comparison u f p (index u f p d.1) ≫ e :=
  localIntertwines u f p e fixRoot (index u f p d.1) (refinedCell u f p d.1)
    (refinedRootEquation u f p d.1) (refinedFactor u f p e d)

end Connected

section Capture

variable (chi : Cardinal.{w}) [Fact chi.IsRegular]
  [HasCardinalFilteredColimits C chi]
  [IsCardinalPresentable D chi] [IsCardinalPresentable E chi]
  [EssentiallySmall.{w} J] [IsCardinalFiltered J chi]
  (e : pushout u f ⟶ pushout u f)
  (fixRoot : pushout.inl u f ≫ e = pushout.inl u f) (he : e ≫ e = e)

include chi fixRoot he in
/-- The complete trace is internally constructed by actual Under capture and eventual equality. -/
theorem nonemptyData : Nonempty (Data u f p e) := by
  let : IsFiltered J := isFiltered_of_isCardinalFiltered J chi
  let : IsConnected J := IsFiltered.isConnected J
  let : IsCardinalPresentable (Under.mk f) chi := underSourcePresentable f chi
  let rooted := CompactRootPushoutPresentation.rootedPresentation u f p
  let m : Under.mk f ⟶ (Under.map u).obj (Under.mk (pushout.inl u f)) :=
    Under.homMk (pushout.inr u f ≫ e) (by
      change f ≫ (pushout.inr u f ≫ e) = u ≫ pushout.inl u f
      rw [← Category.assoc, ← pushout.condition, Category.assoc, fixRoot])
  obtain ⟨j, mj, hmj⟩ := IsCardinalPresentable.exists_hom_of_isColimit chi rooted.isColimit m
  let z : E ⟶ stage u f p j := mj.right
  have hz : f ≫ z = (p.diag.obj j).hom ≫ root u f p j := by
    have hw := Under.w mj
    change f ≫ z = f ≫ cellLeg u f p j at hw
    exact hw.trans pushout.condition.symm
  have hFactor : z ≫ CompactRootPushoutPresentation.comparison u f p j =
      pushout.inr u f ≫ e := by
    have hr := congrArg (fun a => a.right) hmj
    change z ≫ ((CompactRootPushoutPresentation.rootedPresentation u f p).ι.app j).right =
      pushout.inr u f ≫ e at hr
    rw [CompactRootPushoutPresentation.rooted_leg_right] at hr
    exact hr
  let a := localEndomorphism u f p j z hz
  have hInter : a ≫ CompactRootPushoutPresentation.comparison u f p j =
      CompactRootPushoutPresentation.comparison u f p j ≫ e :=
    localIntertwines u f p e fixRoot j z hz hFactor
  have hEq : (z ≫ a) ≫ CompactRootPushoutPresentation.comparison u f p j =
      z ≫ CompactRootPushoutPresentation.comparison u f p j := by
    calc
      _ = z ≫ (a ≫ CompactRootPushoutPresentation.comparison u f p j) :=
        Category.assoc _ _ _
      _ = z ≫ (CompactRootPushoutPresentation.comparison u f p j ≫ e) := by rw [hInter]
      _ = (pushout.inr u f ≫ e) ≫ e := by rw [← Category.assoc, hFactor]
      _ = pushout.inr u f ≫ e := by rw [Category.assoc, he]
      _ = _ := hFactor.symm
  have hEq' : (z ≫ a) ≫ (CompactRootPushoutPresentation.presentation u f p).ι.app j =
      z ≫ (CompactRootPushoutPresentation.presentation u f p).ι.app j := by
    simpa only [CompactRootPushoutPresentation.presentation_leg] using hEq
  obtain ⟨k, h, hh⟩ := IsCardinalPresentable.exists_eq_of_isColimit' chi
    (CompactRootPushoutPresentation.presentation u f p).isColimit (z ≫ a) z hEq'
  let t : Trace u f p := ⟨⟨j, ⟨z, hz⟩⟩, k, h⟩
  refine ⟨⟨t, ?_, ?_⟩⟩
  · exact hFactor
  · change (z ≫ a) ≫ transition u f p h = z ≫ transition u f p h
    change (z ≫ a) ≫ transition u f p h = z ≫ transition u f p h at hh
    exact hh

/-- One actual chosen trace is shared by every exposed initial, refinement and final field. -/
def data : Data u f p e := Classical.choice (nonemptyData u f p chi e fixRoot he)

end Capture

end CategoryTheory.SmallObject.CompactRootIdempotentCapture
