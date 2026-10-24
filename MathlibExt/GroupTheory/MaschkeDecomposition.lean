module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Basic.Complex.Basic

import Mathlib.RepresentationTheory.Maschke

@[expose] public section

set_option linter.style.haveILetI false

open Representation

namespace MathlibExt.GroupTheory.MaschkeDecomposition

/-!
# Maschke's decomposition theorem

Every finite-dimensional complex representation of a finite group is equivalent
to a direct sum of irreducible representations.

Source: `v1/Atlas/AlgebraNotes`, Lecture 2, Maschke's theorem. The v1
formalization `CharacterTheory.maschke_irreducible_decomposition` in
`v1/Atlas/AlgebraNotes/code/Characters.lean` is left as an unproved placeholder
there; the proof below is independent of v1, via Maschke semisimplicity of the
`MonoidAlgebra ℂ G`-module `σ.asModule` and the semisimple decomposition into
simple submodules. Batch 15 (`RepresentationMultiplicity`) assumed such a
decomposition as an explicit hypothesis; this file proves that the decomposition
exists.

The index type is existentially quantified in the same universe as the carrier
`W`, with explicit `Fintype` and `DecidableEq` witnesses (Lean `∃` cannot bind
instances), matching the input shape of `RepresentationMultiplicity`.
-/

/-- If a subrepresentation of `σ` comes from a simple `MonoidAlgebra` submodule,
its restriction is irreducible. The proof lifts an arbitrary subrepresentation
of the restriction back to a subrepresentation of `σ` and uses simplicity of the
`MonoidAlgebra` submodule. -/
private theorem irreducible_toRepresentation_of_simple {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    {S : Submodule (MonoidAlgebra ℂ G) σ.asModule}
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) ↥S) :
    (Subrepresentation.ofSubmodule' S).toRepresentation.IsIrreducible := by
  classical
  haveI hNT : Nontrivial ↥((Subrepresentation.ofSubmodule' S).toSubmodule) :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ↥S
  have hbot_ne_top :
      (⊥ : Subrepresentation (Subrepresentation.ofSubmodule' S).toRepresentation) ≠ ⊤ := by
    intro h
    have h2 := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h2
  haveI : Nontrivial (Subrepresentation (Subrepresentation.ofSubmodule' S).toRepresentation) :=
    ⟨⊥, ⊤, hbot_ne_top⟩
  apply IsSimpleOrder.mk
  intro U
  -- Lift `U` to a subrepresentation `V` of `σ`.
  let V : Subrepresentation σ :=
    { toSubmodule := U.toSubmodule.map (Subrepresentation.ofSubmodule' S).toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro g w hw
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
        refine Submodule.mem_map.mpr
          ⟨(Subrepresentation.ofSubmodule' S).toRepresentation g u,
            U.apply_mem_toSubmodule g hu, ?_⟩
        rfl }
  have hVle : V ≤ Subrepresentation.ofSubmodule' S := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    exact u.2
  have hVas_le : V.asSubmodule ≤ S := by
    intro x hx
    have hx2 : (σ.asModuleEquiv x : W) ∈ V.toSubmodule := hx
    obtain ⟨u, hu, hu2⟩ := Submodule.mem_map.mp hx2
    have hmem : (u : W) ∈ S := Subrepresentation.mem_ofSubmodule'_iff.mp u.2
    rw [Submodule.subtype_apply] at hu2
    rw [hu2] at hmem
    exact hmem
  have hN := hS.eq_bot_or_eq_top (V.asSubmodule.comap S.subtype)
  rcases hN with hN | hN
  · -- Case `⊥`: then `V = ⊥`, hence `U = ⊥`.
    left
    have hVbot : V.asSubmodule = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro x hx
      have hxS : x ∈ S := hVas_le hx
      have hxcomap : (⟨x, hxS⟩ : ↥S) ∈ V.asSubmodule.comap S.subtype := hx
      rw [hN] at hxcomap
      have h0 : (⟨x, hxS⟩ : ↥S) = 0 := (Submodule.mem_bot _).mp hxcomap
      exact congrArg Subtype.val h0
    have hVto : V.toSubmodule = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro w hw
      have hw2 : (σ.asModuleEquiv.symm w) ∈ V.asSubmodule := hw
      rw [hVbot] at hw2
      have h0 := (Submodule.mem_bot _).mp hw2
      exact by simpa using congrArg (⇑σ.asModuleEquiv) h0
    apply Subrepresentation.toSubmodule_injective
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    have huV : ((Subrepresentation.ofSubmodule' S).toSubmodule.subtype u) ∈ V.toSubmodule :=
      Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    rw [hVto] at huV
    have h0 : ((Subrepresentation.ofSubmodule' S).toSubmodule.subtype u) = 0 :=
      (Submodule.mem_bot _).mp huV
    exact Subtype.ext (by simpa using h0)
  · -- Case `⊤`: then `V = T`, hence `U = ⊤`.
    right
    have hVS : S ≤ V.asSubmodule := Submodule.comap_subtype_eq_top.mp hN
    have hVeq : V.asSubmodule = S := le_antisymm hVas_le hVS
    have hVto : V.toSubmodule = (Subrepresentation.ofSubmodule' S).toSubmodule := by
      apply le_antisymm
      · intro w hw
        have hw2 : w ∈ V.asSubmodule := hw
        rw [hVeq] at hw2
        exact hw2
      · intro w hw
        have hw2 : w ∈ V.asSubmodule := by
          rw [hVeq]; exact hw
        exact hw2
    have hVT : V = Subrepresentation.ofSubmodule' S :=
      Subrepresentation.toSubmodule_injective hVto
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_iff'.mpr
    intro u
    have huV : ((Subrepresentation.ofSubmodule' S).toSubmodule.subtype u) ∈ V.toSubmodule := by
      rw [hVto]; exact u.2
    obtain ⟨u', hu', huu'⟩ := Submodule.mem_map.mp huV
    have huu : u' = u := by
      have hsub : (Subrepresentation.ofSubmodule' S).toSubmodule.subtype u' =
          (Subrepresentation.ofSubmodule' S).toSubmodule.subtype u := huu'
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at hsub
      exact Subtype.ext hsub
    exact huu ▸ hu'

/-- Transfer of independence and spanning from a family of `MonoidAlgebra` submodules
to the corresponding family of `ℂ`-submodules of `W`. -/
private theorem iSupIndep_iSup_toSubmodule_of_iSupIndep {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    {ι : Type*} [Fintype ι] (S : ι → Submodule (MonoidAlgebra ℂ G) σ.asModule)
    (hind : iSupIndep S) (hspan : iSup S = ⊤) :
    iSupIndep (fun i => (Subrepresentation.ofSubmodule' (S i)).toSubmodule) ∧
      iSup (fun i => (Subrepresentation.ofSubmodule' (S i)).toSubmodule) = ⊤ := by
  classical
  have hInd : iSupIndep (fun i => (Subrepresentation.ofSubmodule' (S i)).toSubmodule) := by
    intro i
    rw [disjoint_iff]
    rw [(Submodule.eq_bot_iff _)]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    have hx1' : (σ.asModuleEquiv.symm x) ∈ S i := hx1
    have hle : (⨆ j, ⨆ _ : j ≠ i,
          (Subrepresentation.ofSubmodule' (S j)).toSubmodule : Submodule ℂ W) ≤
        ((⨆ j, ⨆ _ : j ≠ i, S j :
          Submodule (MonoidAlgebra ℂ G) σ.asModule).restrictScalars ℂ) := by
      apply iSup_le; intro j
      apply iSup_le; intro hj y hy
      have hyS : y ∈ S j := Subrepresentation.mem_ofSubmodule'_iff.mp hy
      have hsup : S j ≤ ⨆ k, ⨆ _ : k ≠ i, S k :=
        le_trans (le_iSup (fun _ : j ≠ i => S j) hj)
          (le_iSup (fun k => ⨆ _ : k ≠ i, S k) j)
      exact hsup hyS
    have hx2' : (σ.asModuleEquiv.symm x) ∈ ⨆ j, ⨆ _ : j ≠ i, S j := hle hx2
    have hdisj := hind i
    rw [disjoint_iff, (Submodule.eq_bot_iff _)] at hdisj
    have h0 := hdisj _ ⟨hx1', hx2'⟩
    exact by simpa using congrArg (⇑σ.asModuleEquiv) h0
  refine ⟨hInd, ?_⟩
  -- Spanning: the `ℂ`-sup is invariant, so it is a subrepresentation whose `asSubmodule`
  -- contains every `S i`, hence is `⊤`.
  have hUinv : ∀ g, ∀ w ∈ (⨆ i, (Subrepresentation.ofSubmodule' (S i)).toSubmodule :
      Submodule ℂ W), σ g w ∈ (⨆ i, (Subrepresentation.ofSubmodule' (S i)).toSubmodule :
      Submodule ℂ W) := by
    intro g w hw
    have hmap : Submodule.map (σ g)
        (⨆ i, (Subrepresentation.ofSubmodule' (S i)).toSubmodule : Submodule ℂ W) ≤
        (⨆ i, (Subrepresentation.ofSubmodule' (S i)).toSubmodule : Submodule ℂ W) := by
      rw [Submodule.map_iSup]
      apply iSup_le; intro i
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      exact Submodule.mem_comap.mpr (Submodule.mem_iSup_of_mem i
        ((Subrepresentation.ofSubmodule' (S i)).apply_mem_toSubmodule g hx))
    exact hmap ⟨w, hw, rfl⟩
  let U' : Subrepresentation σ :=
    { toSubmodule := (⨆ i, (Subrepresentation.ofSubmodule' (S i)).toSubmodule : Submodule ℂ W)
      apply_mem_toSubmodule := hUinv }
  have hge : iSup S ≤ U'.asSubmodule := by
    apply iSup_le; intro i x hx
    have hxT : (σ.asModuleEquiv x : W) ∈
        (Subrepresentation.ofSubmodule' (S i)).toSubmodule := hx
    have hxU : (σ.asModuleEquiv x : W) ∈
        (⨆ i, (Subrepresentation.ofSubmodule' (S i)).toSubmodule : Submodule ℂ W) :=
      Submodule.mem_iSup_of_mem i hxT
    show (σ.asModuleEquiv x : W) ∈ U'.asSubmodule
    exact Subrepresentation.mem_asSubmodule_iff.mpr hxU
  rw [hspan] at hge
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hx : x ∈ U'.asSubmodule := hge Submodule.mem_top
  exact hx

universe u v

-- The `set_option` below is needed for the `LinearEquiv.ofBijective` step: the
-- `DirectSum.coeLinearMap` definitional unfolding is slow at default transparency,
-- and Mathlib uses the same option for the corresponding `IsInternal` lemmas.
set_option backward.isDefEq.respectTransparency false in
/-- **Maschke's theorem.** Every finite-dimensional complex representation of a
finite group is equivalent to a direct sum of irreducible representations. -/
theorem maschke_decomposition {G : Type v} [Group G] [Fintype G]
    {W : Type u} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (T : ι → Subrepresentation σ),
      (∀ i, (T i).toRepresentation.IsIrreducible) ∧
      Nonempty (Representation.Equiv σ
        (Representation.directSum (fun i => (T i).toRepresentation))) := by
  classical
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ G) σ.asModule := by
    rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    infer_instance
  have hfinM : Module.Finite (MonoidAlgebra ℂ G) σ.asModule := by
    have h1 : Module.Finite ℂ σ.asModule :=
      Module.Finite.of_surjective σ.asModuleEquiv.symm.toLinearMap
        (EquivLike.surjective σ.asModuleEquiv.symm)
    exact Module.Finite.of_restrictScalars_finite ℂ (MonoidAlgebra ℂ G) σ.asModule
  obtain ⟨s, hind, hspan, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (MonoidAlgebra ℂ G) σ.asModule
  have hind' : iSupIndep (fun m : ↥s => (m : Submodule (MonoidAlgebra ℂ G) σ.asModule)) :=
    (sSupIndep_iff _).mp hind
  have hfin : Finite (↥s) := by
    apply WellFoundedGT.finite_of_iSupIndep hind'
    intro m
    haveI : IsSimpleModule (MonoidAlgebra ℂ G) ↥(m : Submodule (MonoidAlgebra ℂ G) σ.asModule) :=
      hsimple _ m.2
    exact (Submodule.nontrivial_iff_ne_bot).mp (IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _)
  letI : Fintype (↥s) := Fintype.ofFinite (↥s)
  have hspan' : iSup (fun m : ↥s => (m : Submodule (MonoidAlgebra ℂ G) σ.asModule)) = ⊤ := by
    rw [← sSup_eq_iSup']
    exact hspan
  obtain ⟨hInd, hTop⟩ := iSupIndep_iSup_toSubmodule_of_iSupIndep σ
    (fun m : ↥s => (m : Submodule (MonoidAlgebra ℂ G) σ.asModule)) hind' hspan'
  set T : ↥s → Subrepresentation σ :=
    fun m => Subrepresentation.ofSubmodule' (m : Submodule (MonoidAlgebra ℂ G) σ.asModule) with hT
  refine ⟨↥s, inferInstance, inferInstance, T, fun m => ?_, ⟨?_⟩⟩
  · exact irreducible_toRepresentation_of_simple σ (hsimple _ m.2)
  · -- The `Equiv` from `IsInternal`, via `DirectSum.coeLinearMap`.
    have hInt : DirectSum.IsInternal (fun m : ↥s => (T m).toSubmodule) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hInd hTop
    let E : (DirectSum ↥s (fun m : ↥s => ↥((T m).toSubmodule))) ≃ₗ[ℂ] W :=
      LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun m : ↥s => (T m).toSubmodule)) hInt
    have hsingle : ∀ (g : G) (i : ↥s) (a : ↥((T i).toSubmodule)),
        E.toLinearMap ((Representation.directSum (fun m : ↥s => (T m).toRepresentation)) g
          (DFinsupp.single i a)) =
        σ g (E.toLinearMap (DFinsupp.single i a)) := by
      intro g i a
      have h1 : (Representation.directSum (fun m : ↥s => (T m).toRepresentation)) g
          (DFinsupp.single i a) = DFinsupp.single i ((T i).toRepresentation g a) := by
        apply DFinsupp.ext
        intro j
        show (DirectSum.lmap (fun m : ↥s => (T m).toRepresentation g)
            (DFinsupp.single (β := fun m : ↥s => ↥((T m).toSubmodule)) i a)) j =
          (DFinsupp.single (β := fun m : ↥s => ↥((T m).toSubmodule)) i
            ((T i).toRepresentation g a)) j
        rw [DirectSum.lmap_apply]
        by_cases hj : j = i
        · subst hj
          simp
        · rw [DFinsupp.single_eq_of_ne hj, DFinsupp.single_eq_of_ne hj, map_zero]
      have e1 : E.toLinearMap (DFinsupp.single i ((T i).toRepresentation g a)) =
          ((T i).toRepresentation g a : W) := DirectSum.coeLinearMap_of _ i _
      have e2 : E.toLinearMap (DFinsupp.single i a) = (a : W) :=
        DirectSum.coeLinearMap_of _ i _
      rw [h1, e1, e2]
      rfl
    have hE : ∀ g : G, E.toLinearMap ∘ₗ
        (Representation.directSum (fun m : ↥s => (T m).toRepresentation)) g =
        σ g ∘ₗ E.toLinearMap := by
      intro g
      apply LinearMap.ext
      intro y
      induction y using DFinsupp.induction with
      | h0 => simp
      | ha i b f _ _ ih =>
        simp only [LinearMap.comp_apply, map_add, hsingle g, ih]
    exact (Representation.Equiv.mk E (fun g => hE g)).symm

end MathlibExt.GroupTheory.MaschkeDecomposition
