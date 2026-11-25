/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.OriginalCompactPushoutRetract
public import Mathlib.CategoryTheory.Presentable.Type

/-!
# An actual compact-retract client with nonmonomorphic original maps

The original generator collapses Bool to Unit. The original larger root is
Nat × Bool, the given retract root is Nat, and their original source
projection is nonmonomorphic. Both roots are noncompact at aleph0.
All Arrow-retract maps are constructed from the original pushouts.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

namespace CategoryTheory.SmallObject.CompactPushoutRetractOwner

open Limits

abbrev chi : Cardinal.{0} := Cardinal.aleph0

local instance regular : Fact chi.IsRegular := Cardinal.fact_isRegular_aleph0

local instance boolPresentable : IsCardinalPresentable Bool chi :=
  (hasCardinalLT_of_finite Bool chi le_rfl).isCardinalPresentable

local instance unitPresentable : IsCardinalPresentable Unit chi :=
  (hasCardinalLT_of_finite Unit chi le_rfl).isCardinalPresentable

/-- The literal nonmonomorphic original generator. -/
def generator : Bool ⟶ Unit := ↾fun _ => ()

/-- The original compact generator root into the noncompact given source. -/
def givenRoot : Bool ⟶ ℕ := ↾fun b => if b then 1 else 0

/-- The actual original source inclusion. -/
def sourceSection : ℕ ⟶ ℕ × Bool := ↾fun n => (n, false)

/-- The actual original source projection. -/
def sourceProjection : ℕ × Bool ⟶ ℕ := ↾fun t => t.1

theorem source_retract : sourceSection ≫ sourceProjection = 𝟙 ℕ := rfl

/-- The larger original root map retains both original maps. -/
abbrev largeRoot : Bool ⟶ ℕ × Bool := givenRoot ≫ sourceSection

/-- The actual given Arrow being retracted. -/
abbrev givenArrow : ℕ ⟶ pushout givenRoot generator := pushout.inl givenRoot generator

/-- The larger original pushout Arrow. -/
abbrev originalArrow : ℕ × Bool ⟶ pushout largeRoot generator :=
  pushout.inl largeRoot generator

/-- The original target section retains the actual source section and generator-target inclusion. -/
def targetSection : pushout givenRoot generator ⟶ pushout largeRoot generator :=
  pushout.desc (sourceSection ≫ originalArrow) (pushout.inr largeRoot generator) (by
    rw [← Category.assoc]
    exact pushout.condition)

/-- The original target projection retains the same source and generator-target functions. -/
def targetProjection : pushout largeRoot generator ⟶ pushout givenRoot generator :=
  pushout.desc (sourceProjection ≫ givenArrow) (pushout.inr givenRoot generator) (by
    rw [largeRoot, Category.assoc, ← Category.assoc sourceSection sourceProjection,
      source_retract, Category.id_comp]
    exact pushout.condition)

theorem given_section : givenArrow ≫ targetSection = sourceSection ≫ originalArrow :=
  pushout.inl_desc _ _ _

theorem original_projection :
    originalArrow ≫ targetProjection = sourceProjection ≫ givenArrow :=
  pushout.inl_desc _ _ _

theorem local_section :
    pushout.inr givenRoot generator ≫ targetSection = pushout.inr largeRoot generator :=
  pushout.inr_desc _ _ _

theorem local_projection :
    pushout.inr largeRoot generator ≫ targetProjection = pushout.inr givenRoot generator :=
  pushout.inr_desc _ _ _

/-- The full original target retract is derived from both actual pushout inclusions. -/
theorem target_retract :
    targetSection ≫ targetProjection = 𝟙 (pushout givenRoot generator) := by
  apply pushout.hom_ext
  · calc
      _ = (givenArrow ≫ targetSection) ≫ targetProjection := (Category.assoc _ _ _).symm
      _ = (sourceSection ≫ originalArrow) ≫ targetProjection := by rw [given_section]
      _ = sourceSection ≫ (sourceProjection ≫ givenArrow) := by
        rw [Category.assoc, original_projection]
      _ = givenArrow := by rw [← Category.assoc, source_retract, Category.id_comp]
      _ = _ := (Category.comp_id _).symm
  · rw [← Category.assoc, local_section, local_projection, Category.comp_id]

/-- A genuine whole Arrow retract with the ORIGINAL nonidentity source components. -/
def originalRetract : RetractArrow givenArrow originalArrow where
  i := Arrow.homMk sourceSection targetSection given_section.symm
  r := Arrow.homMk sourceProjection targetProjection original_projection.symm
  retract := by
    apply Arrow.hom_ext
    · exact source_retract
    · exact target_retract

/-- The original generator is nonmonomorphic; no mono hypothesis can discharge this client. -/
theorem generator_not_mono : ¬ Mono generator := by
  intro hm
  let : Mono generator := hm
  let f₀ : Unit ⟶ Bool := ↾fun _ => false
  let f₁ : Unit ⟶ Bool := ↾fun _ => true
  have he : f₀ ≫ generator = f₁ ≫ generator := rfl
  have h : f₀ = f₁ := (cancel_mono generator).1 he
  have hb : false = true := ConcreteCategory.congr_hom h ()
  cases hb

/-- The actual original source projection is also nonmonomorphic. -/
theorem sourceProjection_not_mono : ¬ Mono sourceProjection := by
  intro hm
  let : Mono sourceProjection := hm
  let f₀ : Unit ⟶ ℕ × Bool := ↾fun _ => (0, false)
  let f₁ : Unit ⟶ ℕ × Bool := ↾fun _ => (0, true)
  have he : f₀ ≫ sourceProjection = f₁ ≫ sourceProjection := rfl
  have h : f₀ = f₁ := (cancel_mono sourceProjection).1 he
  have hp : (0, false) = (0, true) := ConcreteCategory.congr_hom h ()
  have hb : false = true := congrArg (fun t : ℕ × Bool => t.2) hp
  cases hb

/-- Nat is genuinely noncompact at the supplied regular rank. -/
theorem givenSource_not_presentable : ¬ IsCardinalPresentable ℕ chi := by
  intro h
  have hc := (Types.isCardinalPresentable_iff chi).1 h
  have ht : Cardinal.mk ℕ < chi := (hasCardinalLT_iff_cardinal_mk_lt ℕ chi).1 hc
  have hlt : Cardinal.aleph0 < Cardinal.aleph0 := by
    simpa only [chi, Cardinal.mk_nat] using ht
  exact (lt_irrefl _) hlt

/-- The larger original root is also genuinely noncompact. -/
theorem originalSource_not_presentable : ¬ IsCardinalPresentable (ℕ × Bool) chi := by
  intro h
  let R : Retract ℕ (ℕ × Bool) :=
    { i := sourceSection, r := sourceProjection, retract := source_retract }
  exact givenSource_not_presentable (R.isCardinalPresentable chi)

/-- The FULL generic compact-retract construction applies to these original large roots and maps. -/
theorem compactPresentation :
    ∃ (D' L : Type) (_ : IsCardinalPresentable D' chi) (_ : IsCardinalPresentable L chi)
      (alpha : Bool ⟶ D') (v : D' ⟶ ℕ) (_ : alpha ≫ v = givenRoot)
      (f' : D' ⟶ L) (k : L ⟶ pushout givenRoot generator)
      (_ : RetractArrow f' (pushout.inl alpha generator)),
      IsPushout v f' givenArrow k ∧ IsCardinalPresentable (Arrow.mk f') chi := by
  obtain ⟨D', L, hD, hL, alpha, v, hv, f', k, hR, hP, hA⟩ :=
    OriginalCompactPushoutRetract.existsCompactPushout originalRetract largeRoot generator
      (pushout.inr largeRoot generator) (IsPushout.of_hasPushout largeRoot generator) chi
  have hv' : alpha ≫ v = givenRoot := by
    change alpha ≫ v = largeRoot ≫ sourceProjection at hv
    simpa only [largeRoot, Category.assoc, source_retract, Category.comp_id] using hv
  exact ⟨D', L, hD, hL, alpha, v, hv', f', k, hR, hP, hA⟩

/-- The endpoint Iso is constructed from the ORIGINAL actual retract, with no supplied Iso. -/
def givenEndpointIso :
    IdempotentCoequalizerSplit.obj (ArrowRetractRootNormalization.idempotent originalRetract) ≅
      pushout givenRoot generator :=
  ArrowRetractRootNormalization.endpointIso originalRetract

/-- The actual original given Arrow is recovered through both selected endpoint functions. -/
theorem endpoint_root :
    ArrowRetractRootNormalization.root originalRetract ≫
      IdempotentCoequalizerSplit.projection
        (ArrowRetractRootNormalization.idempotent originalRetract) ≫
      givenEndpointIso.hom = givenArrow :=
  ArrowRetractRootNormalization.root_endpoint originalRetract

end CategoryTheory.SmallObject.CompactPushoutRetractOwner
