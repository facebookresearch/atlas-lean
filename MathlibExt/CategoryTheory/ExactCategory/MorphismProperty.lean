/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Admissible morphisms in exact categories

In an additive category `C` with a chosen Quillen exact structure,
admissible monomorphisms and epimorphisms contain identities, are closed
under composition and under isomorphism of arrows, and satisfy the
exact-structure pushout and pullback base-change properties.
-/

@[expose] public section

open CategoryTheory Limits Preadditive ZeroObject

universe v u

namespace CategoryTheory

namespace ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable [ExactCategory C]

section AdmissibleEpiCalculus

private lemma isAdmissibleExact_id_epi (X : C) :
    IsAdmissibleExact (ShortComplex.mk (0 : (0 : C) ⟶ X) (𝟙 X) (by simp)) := by
  let S_split : ShortComplex C :=
    ShortComplex.mk
      (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ X) (biprod.snd : (0 : C) ⊞ X ⟶ X) (by simp)
  have h_split : IsAdmissibleExact S_split := isAdmissibleExact_split (0 : C) X
  have h_iso :
      ShortComplex.mk (0 : (0 : C) ⟶ X) (𝟙 X) (by simp) ≅ S_split :=
    ShortComplex.isoMk (Iso.refl (0 : C)) (isoZeroBiprod (isZero_zero C)) (Iso.refl X)
      ((isZero_zero C).eq_of_src _ _) (by dsimp [S_split]; simp)
  exact isAdmissibleExact_of_iso h_iso.symm h_split

/-- In an additive exact category `C`, the identity of every object `X`
is an admissible epimorphism. It is the quotient map of a split
admissible exact sequence. -/
lemma isAdmissibleEpi_id (X : C) : IsAdmissibleEpi (𝟙 X) :=
  ⟨(0 : C), (0 : (0 : C) ⟶ X), by simp, isAdmissibleExact_id_epi X⟩

/-- In an additive exact category `C`, every isomorphism `f : X → Y`
is an admissible epimorphism, since admissible quotient maps are
stable under isomorphism of arrows. -/
lemma isAdmissibleEpi_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsAdmissibleEpi f := by
  have h_id : IsAdmissibleExact (ShortComplex.mk (0 : (0 : C) ⟶ X) (𝟙 X) (by simp)) :=
    isAdmissibleExact_id_epi X
  let S_id : ShortComplex C := ShortComplex.mk (0 : (0 : C) ⟶ X) (𝟙 X) (by simp)
  let S_f : ShortComplex C := ShortComplex.mk (0 : (0 : C) ⟶ X) f (by simp)
  have h_iso : S_id ≅ S_f :=
    ShortComplex.isoMk (Iso.refl (0 : C)) (Iso.refl X) (asIso f)
      ((isZero_zero C).eq_of_src _ _) (by simp [S_id, S_f])
  have h_f : IsAdmissibleExact S_f := isAdmissibleExact_of_iso h_iso h_id
  exact ⟨(0 : C), (0 : (0 : C) ⟶ X), by simp, h_f⟩

/-- In an additive exact category `C`, the admissible-epimorphism class
is multiplicative: it contains every identity and the composite of
any two composable admissible epimorphisms. -/
instance instIsMultiplicativeAdmissibleEpis :
    (admissibleEpisOf C IsAdmissibleExact).IsMultiplicative where
  id_mem X := isAdmissibleEpi_id X
  comp_mem f g hf hg := admissibleEpi_comp.comp_mem f g hf hg

/-- In an additive exact category `C`, the class of admissible epimorphisms
is invariant under isomorphisms of arrows. Thus replacing either
endpoint through an isomorphism preserves admissibility. -/
instance instRespectsIsoAdmissibleEpis :
    (admissibleEpisOf C IsAdmissibleExact).RespectsIso := by
  have h : (admissibleEpisOf C IsAdmissibleExact).IsStableUnderComposition :=
    admissibleEpi_comp
  exact MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f hf => isAdmissibleEpi_of_isIso f)

namespace IsAdmissibleEpi

/- Proof implementation note.
Identity is an admissible epi (ergonomic alias).
-/

/-- In an additive exact category `C`, the identity `𝟙 X` of each object
`X` is an admissible epimorphism: it occurs as the second map of a
split admissible kernel–cokernel pair. -/
lemma id (X : C) : IsAdmissibleEpi (𝟙 X) := isAdmissibleEpi_id X

/- Proof implementation note.
Isomorphism is an admissible epi (ergonomic alias).
-/

/-- In an additive exact category `C`, an isomorphism `f : X → Y` is an
admissible epimorphism. This is the identity quotient map transported
through the endpoint isomorphism. -/
lemma of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsAdmissibleEpi f :=
  isAdmissibleEpi_of_isIso f

/-- In an additive exact category `C`, every morphism `X → 0` to a
zero object is an admissible epimorphism, arising from the split
sequence `X → X → 0`. -/
lemma toZero {X : C} (f : X ⟶ (0 : C)) : IsAdmissibleEpi f := by
  have h_snd : IsAdmissibleEpi (biprod.snd : X ⊞ (0 : C) ⟶ (0 : C)) :=
    ⟨X, biprod.inl, by simp, isAdmissibleExact_split X (0 : C)⟩
  let e : X ≅ X ⊞ (0 : C) := isoBiprodZero (isZero_zero C)
  have h_e : IsAdmissibleEpi e.hom := isAdmissibleEpi_of_isIso e.hom
  have h_comp : IsAdmissibleEpi (e.hom ≫ biprod.snd : X ⟶ (0 : C)) :=
    admissibleEpi_comp.comp_mem _ _ h_e h_snd
  have h_eq : f = e.hom ≫ biprod.snd := (isZero_zero C).eq_of_tgt _ _
  exact h_eq ▸ h_comp

end IsAdmissibleEpi

end AdmissibleEpiCalculus

section AdmissibleEpiPullback

instance instHasPullbacksAdmissibleEpis :
    (admissibleEpisOf C IsAdmissibleExact).HasPullbacks where
  hasPullback {X Y S} {f : X ⟶ S} (g : Y ⟶ S) hf := by
    obtain ⟨P, fst, snd, hpb, _⟩ :=
      admissibleEpi_pullback (Y := X) (Z := S) (p := f) hf (Z' := Y) (g := g)
    exact @hasPullback_symmetry _ _ _ _ _ g f hpb.hasPullback

instance instIsStableUnderBaseChangeAdmissibleEpis :
    (admissibleEpisOf C IsAdmissibleExact).IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback
    (P := admissibleEpisOf C IsAdmissibleExact) (by
      intro X Y Z f g _ hg
      obtain ⟨P, fst, snd, hpb, hm⟩ :=
        admissibleEpi_pullback (Y := Y) (Z := Z) (p := g) hg (Z' := X) (g := f)
      exact ⟨P, fst, snd, hpb, hm⟩)

end AdmissibleEpiPullback

section AdmissibleMonoPushout

instance instHasPushoutsAdmissibleMonos :
    (admissibleMonosOf C IsAdmissibleExact).HasPushouts where
  hasPushout {X Y S} {f : S ⟶ X} (g : S ⟶ Y) hf := by
    obtain ⟨P, inl, inr, hpo, _⟩ :=
      admissibleMono_pushout (X := S) (Y := X) (i := f) hf (X' := Y) (f := g)
    exact @hasPushout_symmetry _ _ _ _ _ g f hpo.hasPushout

instance instIsStableUnderCobaseChangeAdmissibleMonos :
    (admissibleMonosOf C IsAdmissibleExact).IsStableUnderCobaseChange :=
  MorphismProperty.IsStableUnderCobaseChange.of_forall_exists_isPullback
    (P := admissibleMonosOf C IsAdmissibleExact) (by
      intro X Y Z f g _ hf
      -- `admissibleMono_pushout` yields `IsPushout g f inl inr` with `inl` mono
      -- `IsStableUnderCobaseChange` needs `IsPushout f g`; use `hpo.flip`
      obtain ⟨P, inl, inr, hpo, hm⟩ :=
        admissibleMono_pushout (X := Z) (Y := X) (i := f) hf (X' := Y) (f := g)
      exact ⟨P, inr, inl, hpo.flip, hm⟩)

end AdmissibleMonoPushout

section CrossBaseChange

theorem isAdmissibleMono_of_isPullback {P X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {i : X ⟶ Z} {p : Y ⟶ Z}
    (hpb : IsPullback fst snd i p) (hi : IsAdmissibleMono i)
    (hp : IsAdmissibleEpi p) : IsAdmissibleMono snd := by
  -- keep original mono witness for later `Mono` instance
  have hi_orig := hi
  rcases hi with ⟨Wq, q, w, hS⟩
  have hq : IsAdmissibleEpi q := isAdmissibleEpi_g hS
  have hpq : IsAdmissibleEpi (p ≫ q) :=
    admissibleEpi_comp.comp_mem p q hp hq
  obtain ⟨K, j, w_j, hS_j⟩ := hpq
  have hKernel_j : IsLimit (KernelFork.ofι j w_j) :=
    isLimit_kernelFork_of_isAdmissibleExact hS_j
  have hMono_i : Mono i := IsAdmissibleMono.mono hi_orig
  have w_snd : snd ≫ (p ≫ q) = 0 := by
    calc snd ≫ (p ≫ q) = (snd ≫ p) ≫ q := by rw [Category.assoc]
      _ = (fst ≫ i) ≫ q := by rw [hpb.w]
      _ = fst ≫ (i ≫ q) := by rw [Category.assoc]
      _ = fst ≫ 0 := by rw [w]
      _ = 0 := by simp
  -- show `snd` is kernel of `p ≫ q`
  have hKernel_snd : IsLimit (KernelFork.ofι snd w_snd) := by
    have hKernel_i : IsLimit (KernelFork.ofι i w) :=
      isLimit_kernelFork_of_isAdmissibleExact hS
    refine KernelFork.IsLimit.ofι snd w_snd
      (fun {W'} g' hg' => ?_) (fun {W'} g' hg' => ?_) (fun {W'} g' hg' m hm => ?_)
    · -- lift
      have h₁ : (g' ≫ p) ≫ q = 0 := by
        calc (g' ≫ p) ≫ q = g' ≫ (p ≫ q) := by rw [Category.assoc]
          _ = 0 := hg'
      let s' : KernelFork q := KernelFork.ofι (g' ≫ p) h₁
      let u : W' ⟶ X := hKernel_i.lift s'
      have hu : u ≫ i = g' ≫ p := by
        have hfac := hKernel_i.fac s' WalkingParallelPair.zero
        simpa [s', KernelFork.ofι] using hfac
      exact hpb.lift u g' hu
    · -- fac
      have h₁ : (g' ≫ p) ≫ q = 0 := by
        calc (g' ≫ p) ≫ q = g' ≫ (p ≫ q) := by rw [Category.assoc]
          _ = 0 := hg'
      let s' : KernelFork q := KernelFork.ofι (g' ≫ p) h₁
      let u : W' ⟶ X := hKernel_i.lift s'
      have hu : u ≫ i = g' ≫ p := by
        have hfac := hKernel_i.fac s' WalkingParallelPair.zero
        simpa [s', KernelFork.ofι] using hfac
      change (hpb.lift u g' hu) ≫ snd = g'
      simp [hpb.lift_snd]
    · -- uniq
      have h₁ : (g' ≫ p) ≫ q = 0 := by
        calc (g' ≫ p) ≫ q = g' ≫ (p ≫ q) := by rw [Category.assoc]
          _ = 0 := hg'
      let s' : KernelFork q := KernelFork.ofι (g' ≫ p) h₁
      let u : W' ⟶ X := hKernel_i.lift s'
      have hu : u ≫ i = g' ≫ p := by
        have hfac := hKernel_i.fac s' WalkingParallelPair.zero
        simpa [s', KernelFork.ofι] using hfac
      let v : W' ⟶ P := hpb.lift u g' hu
      have hv_fst : v ≫ fst = u := by simp [v, hpb.lift_fst]
      have hv_snd : v ≫ snd = g' := by simp [v, hpb.lift_snd]
      have hm_snd : m ≫ snd = v ≫ snd := by rw [hm, hv_snd]
      have hm_fst : m ≫ fst = v ≫ fst := by
        have h_eq : (m ≫ fst) ≫ i = (v ≫ fst) ≫ i := by
          calc (m ≫ fst) ≫ i = m ≫ (fst ≫ i) := by rw [Category.assoc]
            _ = m ≫ (snd ≫ p) := by rw [hpb.w]
            _ = (m ≫ snd) ≫ p := by rw [Category.assoc]
            _ = g' ≫ p := by rw [hm]
            _ = u ≫ i := hu.symm
            _ = (v ≫ fst) ≫ i := by rw [hv_fst]
        exact (cancel_mono i).mp h_eq
      exact hpb.hom_ext hm_fst hm_snd
  -- now `snd` and `j` are two kernels of the same map, hence isomorphic
  have hS_snd : IsAdmissibleExact (ShortComplex.mk snd (p ≫ q) w_snd) := by
    let e : P ≅ K :=
      IsLimit.conePointUniqueUpToIso hKernel_snd hKernel_j
    have h_comm₁ : e.hom ≫ j = snd := by
      have h := IsLimit.conePointUniqueUpToIso_hom_comp
        hKernel_snd hKernel_j WalkingParallelPair.zero
      simpa [KernelFork.ofι] using h
    have h_comm₁' : e.hom ≫ j = snd ≫ (Iso.refl Y).hom := by
      have : snd ≫ (Iso.refl Y).hom = snd := by simp
      rw [this]
      exact h_comm₁
    have h_comm₂' : (Iso.refl Y).hom ≫ (p ≫ q) = (p ≫ q) ≫ (Iso.refl Wq).hom := by
      simp
    let S_snd : ShortComplex C := ShortComplex.mk snd (p ≫ q) w_snd
    let S_j : ShortComplex C := ShortComplex.mk j (p ≫ q) w_j
    have h_iso : S_snd ≅ S_j :=
      ShortComplex.isoMk e (Iso.refl Y) (Iso.refl Wq) h_comm₁' h_comm₂'
    exact isAdmissibleExact_of_iso h_iso.symm hS_j
  exact ⟨Wq, p ≫ q, w_snd, hS_snd⟩

instance instIsStableUnderBaseChangeAgainst_mono_epi :
    (admissibleMonosOf C IsAdmissibleExact).IsStableUnderBaseChangeAgainst
      (admissibleEpisOf C IsAdmissibleExact) where
  isStableUnderBaseChangeAlong {X Y} (f : X ⟶ Y) hf := by
    constructor
    intro Z W f' g' g pb hg
    -- `pb : IsPullback f' g' g f` with `g : Z → Y` mono, `f : X → Y` epi
    -- conclusion `P g'` where `g' : W → X` should be mono
    exact isAdmissibleMono_of_isPullback pb hg hf

end CrossBaseChange

end ExactCategory

end CategoryTheory
