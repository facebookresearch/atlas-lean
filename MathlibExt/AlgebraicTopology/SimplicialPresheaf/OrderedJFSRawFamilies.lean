/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompleteness
import MathlibExt.AlgebraicTopology.SimplicialObject.FinitePowerSite
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Basic
import Mathlib.Logic.Small.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialPresheaf.OrderedJFS

/-- Coordinates other than the selected original position. -/
abbrev OtherCoord (n : ℕ) (i : Fin n) := {j : Fin n // j ≠ i}

/-- Full Segal labels retain the source's arity-one members. -/
structure FullSegalIndex (n : ℕ) where
  /-- The selected original simplex coordinate. -/
  coord : Fin n
  /-- The full original spine arity, including arity one. -/
  arity : ℕ
  arity_pos : 1 ≤ arity
  /-- Arbitrary arities at every other original coordinate. -/
  otherIndex : OtherCoord n coord → ℕ

/-- Normalized Segal labels remove only the arity-one redundancy. -/
structure SegalIndex (n : ℕ) where
  /-- The selected original simplex coordinate. -/
  coord : Fin n
  /-- The normalized original spine arity. -/
  arity : ℕ
  arity_ge : 2 ≤ arity
  /-- Arbitrary arities at every other original coordinate. -/
  otherIndex : OtherCoord n coord → ℕ

/-- Completeness labels keep every other original coordinate. -/
structure CompletenessIndex (n : ℕ) where
  /-- The original finite-completeness coordinate. -/
  coord : Fin n
  /-- All other original arities, with no later-tail restriction. -/
  otherIndex : OtherCoord n coord → ℕ

/-- Ordered full constancy has arbitrary earlier and strictly later tuples. -/
structure FullConstancyIndex (n : ℕ) where
  /-- The original selected coordinate fixed at the zero representable. -/
  coord : Fin n
  /-- Arbitrary earlier arities retained by the original arrow. -/
  earlierIndex : {j : Fin n // j.val < coord.val} → ℕ
  /-- All strictly later arities collapsed simultaneously to zero. -/
  laterIndex : {j : Fin n // coord.val < j.val} → ℕ

/-- The normalized constancy witness is exactly a nonzero strictly later entry. -/
structure ConstancyIndex (n : ℕ) where
  /-- The original selected coordinate fixed at the zero representable. -/
  coord : Fin n
  /-- Arbitrary earlier arities retained by the normalized arrow. -/
  earlierIndex : {j : Fin n // j.val < coord.val} → ℕ
  /-- All strictly later arities collapsed simultaneously to zero. -/
  laterIndex : {j : Fin n // coord.val < j.val} → ℕ
  nonzeroLater : ∃ j, laterIndex j ≠ 0

/-- The exact three full branches, with no completeness redundancy. -/
abbrev FullGenerator (n : ℕ) :=
  FullSegalIndex n ⊕ CompletenessIndex n ⊕ FullConstancyIndex n

/-- The source's normalized three branches. -/
abbrev Generator (n : ℕ) := SegalIndex n ⊕ CompletenessIndex n ⊕ ConstancyIndex n

/-- Native Type0 label smallness works in every original coefficient universe. -/
instance fullGeneratorSmall (n : ℕ) : Small.{u} (FullGenerator n) := inferInstance

/-- Native Type0 normalized label smallness needs no outcome assumption. -/
instance generatorSmall (n : ℕ) : Small.{u} (Generator n) := inferInstance

/-- Height zero has no active coordinate in any full branch. -/
instance fullGeneratorZeroEmpty : IsEmpty (FullGenerator 0) where
  false x := by
    rcases x with s | c | c
    · exact Fin.elim0 s.coord
    · exact Fin.elim0 c.coord
    · exact Fin.elim0 c.coord

/-- Height zero likewise has no normalized generator. -/
instance generatorZeroEmpty : IsEmpty (Generator 0) where
  false x := by
    rcases x with s | c | c
    · exact Fin.elim0 s.coord
    · exact Fin.elim0 c.coord
    · exact Fin.elim0 c.coord

/-- Height one admits no nonzero strictly later constancy coordinate. -/
instance constancyOneEmpty : IsEmpty (ConstancyIndex 1) where
  false c := by
    obtain ⟨j, _⟩ := c.nonzeroLater
    have hpos : 0 < j.val.val := Nat.lt_of_le_of_lt (Nat.zero_le _) j.property
    exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt hpos)) j.val.isLt

/-- Normalization is actual weakening of the Segal bound and forgetting one witness. -/
def normalizedToFull {n : ℕ} : Generator n → FullGenerator n
  | .inl s => .inl ⟨s.coord, s.arity, Nat.le_trans (by decide) s.arity_ge, s.otherIndex⟩
  | .inr (.inl c) => .inr (.inl c)
  | .inr (.inr c) => .inr (.inr ⟨c.coord, c.earlierIndex, c.laterIndex⟩)

/-- The ordered original diagram carrier, in the unchanged value universe. -/
abbrev Multi (n : ℕ) := FinitePowerSite.Index n ⥤ SSet.{u}

/-- A finite external product keeps every original outer and inner operator. -/
def productDiagram {n : ℕ} (X : Fin n → SimplicialObject SSet.{u}) : Multi.{u} n where
  obj a :=
    { obj := fun Δ => ∀ i, ((X i).obj (a i)).obj Δ
      map := fun δ => ↾fun x i => ((X i).obj (a i)).map δ (x i)
      map_id := fun Δ => by ext x i; simp
      map_comp := fun δ ε => by ext x i; simp }
  map f :=
    { app := fun Δ => ↾fun x i => ((X i).map (f i)).app Δ (x i)
      naturality := fun Δ Λ δ => by
        ext x i
        exact congrArg (fun h => h (x i)) (((X i).map (f i)).naturality δ) }
  map_id := fun a => by ext Δ x i; simp
  map_comp := fun f g => by ext Δ x i; simp

/-- Product maps retain the original map at every selected coordinate. -/
def productMap {n : ℕ} {X Y : Fin n → SimplicialObject SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) : productDiagram X ⟶ productDiagram Y where
  app a :=
    { app := fun Δ => ↾fun x i => ((f i).app (a i)).app Δ (x i)
      naturality := fun Δ Λ δ => by
        apply ConcreteCategory.hom_ext
        intro x
        funext i
        exact congrArg (fun h => h (x i)) (((f i).app (a i)).naturality δ) }
  naturality a b φ := by
    apply NatTrans.ext
    funext Δ
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    have h := (f i).naturality (φ i)
    exact congrArg (fun k => (k.app Δ) (x i)) h

/-- Original products of actual arrows, without a generation/class outcome. -/
def productArrow {n : ℕ} (f : Fin n → Arrow (SimplicialObject SSet.{u})) :
    Arrow (Multi.{u} n) := Arrow.mk (productMap (fun i => (f i).hom))

/-- The full Segal branch carries the original spine at exactly its active coordinate. -/
def fullSegalComponents {n : ℕ} (s : FullSegalIndex n) (i : Fin n) :
    Arrow (SimplicialObject SSet.{u}) :=
  if h : i = s.coord then Arrow.mk (SSet.Rezk.segalMap.{u} s.arity)
  else Arrow.mk (𝟙 (SSet.Rezk.representable.{u} (s.otherIndex ⟨i, h⟩)))

/-- The completeness branch retains the SAME canonical finite K and kappa. -/
def completenessComponents {n : ℕ} (c : CompletenessIndex n) (i : Fin n) :
    Arrow (SimplicialObject SSet.{u}) :=
  if h : i = c.coord then Arrow.mk SSet.Rezk.FiniteCompleteness.kappa.{u}
  else Arrow.mk (𝟙 (SSet.Rezk.representable.{u} (c.otherIndex ⟨i, h⟩)))

/-- Constancy leaves earlier indices fixed, fixes the selected zero, and collapses all later
ones. -/
def fullConstancyComponents {n : ℕ} (c : FullConstancyIndex n) (i : Fin n) :
    Arrow (SimplicialObject SSet.{u}) :=
  if h : c.coord.val < i.val then
    Arrow.mk (SSet.Rezk.FiniteCompleteness.representableCollapse.{u} (c.laterIndex ⟨i, h⟩))
  else if h : i.val < c.coord.val then
    Arrow.mk (𝟙 (SSet.Rezk.representable.{u} (c.earlierIndex ⟨i, h⟩)))
  else Arrow.mk (𝟙 (SSet.Rezk.representable.{u} 0))

/-- The selected Segal component is the actual original spine inclusion. -/
theorem fullSegal_selected {n : ℕ} (s : FullSegalIndex n) :
    fullSegalComponents.{u} s s.coord = Arrow.mk (SSet.Rezk.segalMap s.arity) := by
  simp [fullSegalComponents]

/-- Every nonselected Segal coordinate retains its arbitrary original representable. -/
theorem fullSegal_other {n : ℕ} (s : FullSegalIndex n) (j : Fin n) (h : j ≠ s.coord) :
    fullSegalComponents.{u} s j =
      Arrow.mk (𝟙 (SSet.Rezk.representable (s.otherIndex ⟨j, h⟩))) := by
  simp [fullSegalComponents, h]

/-- The selected completeness coordinate uses the SAME canonical K-to-zero map. -/
theorem completeness_selected {n : ℕ} (c : CompletenessIndex n) :
    completenessComponents.{u} c c.coord =
      Arrow.mk SSet.Rezk.FiniteCompleteness.kappa := by
  simp [completenessComponents]

/-- Completeness keeps every nonselected coordinate at its supplied original arity. -/
theorem completeness_other {n : ℕ} (c : CompletenessIndex n) (j : Fin n) (h : j ≠ c.coord) :
    completenessComponents.{u} c j =
      Arrow.mk (𝟙 (SSet.Rezk.representable (c.otherIndex ⟨j, h⟩))) := by
  simp [completenessComponents, h]

/-- Every strictly later coordinate collapses in the SAME simultaneous constancy arrow. -/
theorem fullConstancy_later {n : ℕ} (c : FullConstancyIndex n) (j : Fin n)
    (h : c.coord.val < j.val) :
    fullConstancyComponents.{u} c j =
      Arrow.mk (SSet.Rezk.FiniteCompleteness.representableCollapse (c.laterIndex ⟨j, h⟩)) := by
  simp [fullConstancyComponents, h]

/-- Arbitrary earlier coordinates are retained, rather than collapsed or permuted. -/
theorem fullConstancy_earlier {n : ℕ} (c : FullConstancyIndex n) (j : Fin n)
    (h : j.val < c.coord.val) :
    fullConstancyComponents.{u} c j =
      Arrow.mk (𝟙 (SSet.Rezk.representable (c.earlierIndex ⟨j, h⟩))) := by
  simp [fullConstancyComponents, h, Nat.not_lt_of_ge (Nat.le_of_lt h)]

/-- The active constancy coordinate is exactly F(0) with its identity. -/
theorem fullConstancy_selected {n : ℕ} (c : FullConstancyIndex n) :
    fullConstancyComponents.{u} c c.coord = Arrow.mk (𝟙 (SSet.Rezk.representable 0)) := by
  simp [fullConstancyComponents]

/-- Exhaustive original full dispatcher, at every height and coefficient universe. -/
def fullMultiFamily {n : ℕ} : FullGenerator n → Arrow (Multi.{u} n)
  | .inl s => productArrow (fullSegalComponents s)
  | .inr (.inl c) => productArrow (completenessComponents c)
  | .inr (.inr c) => productArrow (fullConstancyComponents c)

/-- Normalized arrows are literal restriction through the original label map. -/
def multiFamily {n : ℕ} (g : Generator n) : Arrow (Multi.{u} n) :=
  fullMultiFamily (normalizedToFull g)

/-- The literal original presheaf carrier, with one opposite on the simplex source. -/
abbrev Original (n : ℕ) := SimplicialPresheaf.{u} (FinitePowerSite.Source n)

/-- Actual full original Arrow values are produced by the existing whole site equivalence. -/
def fullOriginalFamily (n : ℕ) (g : FullGenerator n) : Arrow (Original.{u} n) :=
  (FinitePowerSite.diagramEquiv n SSet.{u}).inverse.mapArrow.obj (fullMultiFamily g)

/-- Actual normalized original Arrow values use exactly the same transport and labels. -/
def originalFamily (n : ℕ) (g : Generator n) : Arrow (Original.{u} n) :=
  fullOriginalFamily n (normalizedToFull g)

/-- Full and normalized branch restriction is actual whole-Arrow equality. -/
theorem originalFamily_toFull (n : ℕ) (g : Generator n) :
    originalFamily.{u} n g = fullOriginalFamily n (normalizedToFull g) := rfl

/-- Every coefficient product point keeps its original coordinate arrow. -/
theorem productArrow_point {n : ℕ} (f : Fin n → Arrow (SimplicialObject SSet.{u}))
    (a : FinitePowerSite.Index n) (Δ : SimplexCategoryᵒᵖ)
    (x : ∀ i, ((f i).left.obj (a i)).obj Δ) :
    (((productArrow f).hom.app a).app Δ x) =
      fun i => ((f i).hom.app (a i)).app Δ (x i) := rfl

/-- The SAME transported full arrow retains both original endpoint maps of the counit. -/
theorem fullTransportCounit (n : ℕ) (g : FullGenerator n) :
    let E := FinitePowerSite.diagramEquiv n SSet.{u}
    let e := (Functor.mapArrowEquivalence E).counitIso.app (fullMultiFamily g)
    e.hom.left ≫ (fullMultiFamily g).hom =
        E.functor.map (fullOriginalFamily n g).hom ≫ e.hom.right ∧
      e.inv.left ≫ E.functor.map (fullOriginalFamily n g).hom =
        (fullMultiFamily g).hom ≫ e.inv.right := by
  dsimp only
  let E := FinitePowerSite.diagramEquiv n SSet.{u}
  let e := (Functor.mapArrowEquivalence E).counitIso.app (fullMultiFamily g)
  exact ⟨e.hom.w, e.inv.w⟩

end SimplicialPresheaf.OrderedJFS
