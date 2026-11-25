/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Field.Rat
public import Mathlib.CategoryTheory.Abelian.Exact
public import MathlibExt.CategoryTheory.ExactCategory.Basic

/-!
# Concrete clients of the exact-category API

The usual short exact sequences give an actual exact structure on
`ModuleCat ℚ`. This test-local instance uses Mathlib's native kernels,
cokernels, pushouts and pullbacks. The split sequence `ℚ ⟶ ℚ ⊞ ℚ ⟶ ℚ`
has nonzero legs and exercises the source API without an assumed
`ExactCategory` instance or additional axioms.
-/

@[expose] public section

namespace MathlibExtTest.CategoryTheory.ExactCategory.BasicClients

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.ExactCategory

noncomputable section

private lemma shortExact_monos_iff {X Y : ModuleCat ℚ} (i : X ⟶ Y) :
    admissibleMonosOf (ModuleCat ℚ) ShortComplex.ShortExact i ↔ Mono i := by
  constructor
  · rintro ⟨_, _, _, h⟩
    exact h.mono_f
  · intro hi
    let := hi
    refine ⟨cokernel i, cokernel.π i, cokernel.condition i, ?_⟩
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i)
      inferInstance inferInstance

private lemma shortExact_epis_iff {Y Z : ModuleCat ℚ} (p : Y ⟶ Z) :
    admissibleEpisOf (ModuleCat ℚ) ShortComplex.ShortExact p ↔ Epi p := by
  constructor
  · rintro ⟨_, _, _, h⟩
    exact h.epi_g
  · intro hp
    let := hp
    refine ⟨kernel p, kernel.ι p, kernel.condition p, ?_⟩
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p)
      inferInstance inferInstance

-- This fixture is deliberately specialized, not a new production adapter.
@[instance_reducible]
private def rationalExactCategory : ExactCategory (ModuleCat ℚ) where
  IsAdmissibleExact := ShortComplex.ShortExact
  shortExact_of_isAdmissibleExact {_} h := h
  isLimit_kernelFork {_} h := ⟨h.fIsKernel⟩
  isColimit_cokernelCofork {_} h := ⟨h.gIsCokernel⟩
  isAdmissibleExact_of_iso {_ _} e h := ShortComplex.shortExact_of_iso e h
  isAdmissibleExact_split X Y :=
    (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact
  admissibleMono_comp := {
    comp_mem := fun i j hi hj => by
      let := (shortExact_monos_iff i).1 hi
      let := (shortExact_monos_iff j).1 hj
      exact (shortExact_monos_iff (i ≫ j)).2 inferInstance }
  admissibleEpi_comp := {
    comp_mem := fun p q hp hq => by
      let := (shortExact_epis_iff p).1 hp
      let := (shortExact_epis_iff q).1 hq
      exact (shortExact_epis_iff (p ≫ q)).2 inferInstance }
  admissibleMono_pushout X Y i hi X' f := by
    let := (shortExact_monos_iff i).1 hi
    exact ⟨pushout f i, pushout.inl f i, pushout.inr f i,
      IsPushout.of_hasPushout f i,
      (shortExact_monos_iff (pushout.inl f i)).2 inferInstance⟩
  admissibleEpi_pullback Y Z p hp Z' g := by
    let := (shortExact_epis_iff p).1 hp
    exact ⟨pullback g p, pullback.fst g p, pullback.snd g p,
      IsPullback.of_hasPullback g p,
      (shortExact_epis_iff (pullback.fst g p)).2 inferInstance⟩

attribute [local instance] rationalExactCategory

private abbrev Line : ModuleCat ℚ := ModuleCat.of ℚ ℚ

private def doubleLine : Line ⟶ Line := 𝟙 Line + 𝟙 Line

private abbrev splitLine : ShortComplex (ModuleCat ℚ) :=
  ShortComplex.mk (biprod.inl : Line ⟶ Line ⊞ Line)
    biprod.snd (by simp)

private lemma line_id_ne_zero : 𝟙 Line ≠ (0 : Line ⟶ Line) := by
  intro h
  have impossible : (1 : ℚ) = 0 :=
    congrArg (fun f : Line ⟶ Line => f.hom (1 : ℚ)) h
  exact one_ne_zero impossible

-- Retained lemmas keep the client proofs visible to the compiled policy audit.
private lemma line_not_isZero : ¬ IsZero Line := by
  intro h
  exact line_id_ne_zero (h.eq_of_src _ _)

private lemma doubleLine_ne_zero : doubleLine ≠ 0 := by
  intro h
  have impossible : (2 : ℚ) = 0 := by
    simpa [doubleLine] using
      congrArg (fun f : Line ⟶ Line => f.hom (1 : ℚ)) h
  exact (by decide : (2 : ℚ) ≠ 0) impossible

private lemma splitLine_admissible : IsAdmissibleExact splitLine :=
  isAdmissibleExact_split Line Line

private lemma splitLine_f_ne_zero : splitLine.f ≠ 0 := by
  intro h
  apply line_id_ne_zero
  simpa [splitLine] using
    congrArg (fun i : Line ⟶ Line ⊞ Line => i ≫ biprod.fst) h

private lemma splitLine_g_ne_zero : splitLine.g ≠ 0 := by
  intro h
  apply line_id_ne_zero
  simpa [splitLine] using
    congrArg (fun p : Line ⊞ Line ⟶ Line => biprod.inr ≫ p) h

private lemma splitLine_shortExact : splitLine.ShortExact :=
  shortExact_of_isAdmissibleExact splitLine_admissible

-- Use the chosen kernel witness to factor any compatible map uniquely.
private lemma splitLine_kernel_lift (k : Line ⟶ Line ⊞ Line)
    (hk : k ≫ splitLine.g = 0) : ∃! lift : Line ⟶ Line,
      lift ≫ splitLine.f = k := by
  obtain ⟨lift, hlift⟩ := KernelFork.IsLimit.lift'
    (isLimit_kernelFork_of_isAdmissibleExact splitLine_admissible) k hk
  let := (isAdmissibleMono_f splitLine_admissible).mono
  refine ⟨lift, hlift, ?_⟩
  intro other hother
  exact (cancel_mono splitLine.f).1 (hother.trans hlift.symm)

-- Dually, use the chosen cokernel witness and prove uniqueness of descent.
private lemma splitLine_cokernel_desc (p : Line ⊞ Line ⟶ Line)
    (hp : splitLine.f ≫ p = 0) : ∃! desc : Line ⟶ Line,
      splitLine.g ≫ desc = p := by
  obtain ⟨desc, hdesc⟩ := CokernelCofork.IsColimit.desc'
    (isColimit_cokernelCofork_of_isAdmissibleExact splitLine_admissible) p hp
  let := (isAdmissibleEpi_g splitLine_admissible).epi
  refine ⟨desc, hdesc, ?_⟩
  intro other hother
  exact (cancel_epi splitLine.g).1 (hother.trans hdesc.symm)

-- Reconstruct a different short complex using the native chosen cokernel,
-- rather than passing admissible exactness as the desired conclusion.
private lemma nativeCokernel_admissible : IsAdmissibleExact
    (ShortComplex.mk splitLine.f (cokernel.π splitLine.f)
      (cokernel.condition splitLine.f)) :=
  isAdmissibleExact_of_isAdmissibleMono_isColimit
    (isAdmissibleMono_f (S := splitLine) splitLine_admissible)
    (cokernelIsCokernel splitLine.f)

-- Exercise the pushout field along multiplication by two and its descent
-- witness. The new admissible mono has a retraction onto the nonzero line.
private lemma pushout_doubleLine :
    ∃ (P : ModuleCat ℚ) (inl : Line ⟶ P) (inr : Line ⊞ Line ⟶ P),
    IsPushout doubleLine splitLine.f inl inr ∧ IsAdmissibleMono inl ∧
      ∃ desc : P ⟶ Line,
        inl ≫ desc = 𝟙 Line ∧ inr ≫ desc = biprod.fst ≫ doubleLine := by
  obtain ⟨P, inl, inr, hP, hi⟩ := admissibleMono_pushout
    Line (Line ⊞ Line) splitLine.f
    (isAdmissibleMono_f splitLine_admissible) Line doubleLine
  exact ⟨P, inl, inr, hP, hi,
    hP.exists_desc (𝟙 Line) (biprod.fst ≫ doubleLine) (by simp)⟩

-- Exercise the pullback field and its lift witness; the new admissible epi
-- has a section from the nonzero line.
private lemma pullback_doubleLine :
    ∃ (P : ModuleCat ℚ) (fst : P ⟶ Line) (snd : P ⟶ Line ⊞ Line),
    IsPullback fst snd doubleLine splitLine.g ∧ IsAdmissibleEpi fst ∧
      ∃ lift : Line ⟶ P,
        lift ≫ fst = 𝟙 Line ∧ lift ≫ snd = doubleLine ≫ biprod.inr := by
  obtain ⟨P, fst, snd, hP, hp⟩ := admissibleEpi_pullback
    (Line ⊞ Line) Line splitLine.g
    (isAdmissibleEpi_g splitLine_admissible) Line doubleLine
  exact ⟨P, fst, snd, hP, hp,
    hP.exists_lift (𝟙 Line) (doubleLine ≫ biprod.inr) (by simp)⟩

end

end MathlibExtTest.CategoryTheory.ExactCategory.BasicClients
