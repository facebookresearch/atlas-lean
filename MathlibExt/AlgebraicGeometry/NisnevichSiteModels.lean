/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed source port from TauCeti, commit62bbc0596dc3539d488232e4e924a338548ea0a9.
Original Apache 2.0 license and author credit are retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicGeometry/Sites/Nisnevich/Basic.lean
Only module and namespace paths are adapted for Atlas.
-/

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import MathlibExt.AlgebraicGeometry.NisnevichResidueFieldModels

/-!
# Nisnevich coverings and the Nisnevich topology

A family of étale morphisms `{pᵢ : Xᵢ ⟶ S}` is a *Nisnevich covering* if every point `s` of `S`
has a preimage `x` in some `Xᵢ` at which `pᵢ` induces an isomorphism of residue fields
`κ(s) ≅ κ(x)`. Nisnevich coverings are stable under base change and composition, and contain the
isomorphisms, so they form a precoverage on the category of schemes; the *Nisnevich topology* is
the Grothendieck topology it generates. It lies between the Zariski and the étale topologies, and
it is subcanonical.

## Main definitions

* `MathlibExt.NisSource.AlgebraicGeometry.Scheme.IsNisnevichCovering f`: the family `f` of
  morphisms into `S`
  is a Nisnevich covering.
* `MathlibExt.NisSource.AlgebraicGeometry.Scheme.nisnevichPrecoverage`: the Nisnevich precoverage
  on schemes.
* `MathlibExt.NisSource.AlgebraicGeometry.Scheme.nisnevichTopology`: the big Nisnevich topology.
* `AlgebraicGeometry.Scheme.smallNisnevichTopology X`: the small Nisnevich site of `X`, on the
  category `X.Etale` of schemes étale over `X`.

## Main results

* `MathlibExt.NisSource.AlgebraicGeometry.Scheme.isNisnevichCovering_of_zariski`: Zariski
  coverings are
  Nisnevich coverings.
* `MathlibExt.NisSource.AlgebraicGeometry.Scheme.IsNisnevichCovering.of_isPullback`,
  `MathlibExt.NisSource.AlgebraicGeometry.Scheme.IsNisnevichCovering.pullback` and
  `MathlibExt.NisSource.AlgebraicGeometry.Scheme.IsNisnevichCovering.comp`: stability under base
change and
  composition.
* `MathlibExt.NisSource.AlgebraicGeometry.Scheme.zariskiTopology_le_nisnevichTopology` and
  `MathlibExt.NisSource.AlgebraicGeometry.Scheme.nisnevichTopology_le_etaleTopology`: the
Nisnevich topology is
  finer than the Zariski topology and coarser than the étale topology.
* `MathlibExt.NisSource.AlgebraicGeometry.Scheme.ofArrows_mem_nisnevichPrecoverage_iff`: a family
  generates a
  covering presieve of the Nisnevich precoverage if and only if it is a Nisnevich covering.
* `MathlibExt.NisSource.AlgebraicGeometry.Scheme.mem_nisnevichTopology_iff`: a sieve is a
  Nisnevich covering
  sieve if and only if it contains a Nisnevich covering family.
* `AlgebraicGeometry.Scheme.ofArrows_mem_smallNisnevichTopology_iff` and
  `AlgebraicGeometry.Scheme.mem_smallNisnevichTopology_iff`: a family in `X.Etale` generates a
  covering sieve of the small Nisnevich site if and only if its underlying morphisms of schemes
  form a Nisnevich covering, and a sieve covers if and only if it contains such a family.
* `AlgebraicGeometry.Scheme.smallNisnevichTopology_le_smallEtaleTopology`: the small Nisnevich
  topology is coarser than the small étale topology.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999),
  §3.1, Proposition 1.1 and Definition 1.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace MathlibExt.NisSource.AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- A family `{pᵢ : Xᵢ ⟶ S}` of morphisms of schemes is a *Nisnevich covering* if every `pᵢ` is
étale and every point `s` of `S` has a preimage `x` in some `Xᵢ` at which `pᵢ` induces an
isomorphism of residue fields `κ(s) ≅ κ(x)`. Morel–Voevodsky, §3.1, Definition 1.2. -/
structure IsNisnevichCovering {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) : Prop where
  /-- Every morphism of a Nisnevich covering is étale. -/
  etale (i : ι) : Etale (f i)
  /-- Every point of the base has a preimage with the same residue field. -/
  exists_isIso (s : S) : ∃ i, ∃ x : X i, f i x = s ∧ IsIso ((f i).residueFieldMap x)

namespace IsNisnevichCovering

variable {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- A Nisnevich covering is jointly surjective. -/
theorem exists_eq (hf : IsNisnevichCovering f) (s : S) : ∃ i, ∃ x : X i, f i x = s := by
  obtain ⟨i, x, hx, -⟩ := hf.exists_isIso s
  exact ⟨i, x, hx⟩

/-- Nisnevich coverings are stable under base change: if `{pᵢ : Xᵢ ⟶ S}` is a Nisnevich covering
and each `Pᵢ` is the fibre product of `Xᵢ` and `Y` over `S`, then `{Pᵢ ⟶ Y}` is a Nisnevich
covering. -/
theorem of_isPullback (hf : IsNisnevichCovering f) {Y : Scheme.{u}} (g : Y ⟶ S)
    {P : ι → Scheme.{u}} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) : IsNisnevichCovering p₁ where
  etale i := have := hf.etale i; MorphismProperty.of_isPullback (P := @Etale) (h i).flip this
  exists_isIso y := by
    obtain ⟨i, x, hx, hiso⟩ := hf.exists_isIso (g y)
    obtain ⟨z, hz₁, hz₂⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := g) (g := f i) y x hx.symm
    have : IsIso ((f i).residueFieldMap (pullback.snd g (f i) z)) := by rwa [hz₂]
    have hfst := AlgebraicGeometry.Scheme.Pullback.isIso_residueFieldMap_fst z
    obtain ⟨e, he⟩ : ∃ e : P i ≅ Limits.pullback g (f i), e.hom ≫ pullback.fst g (f i) = p₁ i :=
      ⟨_, (h i).isoPullback_hom_fst⟩
    have hz : e.hom (e.inv z) = z := by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    refine ⟨i, e.inv z, ?_, ?_⟩
    · rw [← he, Scheme.Hom.comp_apply, hz, hz₁]
    · generalize e.inv z = w at hz
      subst hz
      rw [← he, Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' hfst inferInstance

/-- The base change of a Nisnevich covering of `S` along `g : Y ⟶ S` is a Nisnevich covering
of `Y`. -/
theorem pullback (hf : IsNisnevichCovering f) {Y : Scheme.{u}} (g : Y ⟶ S) :
    IsNisnevichCovering (fun i ↦ Limits.pullback.fst g (f i)) :=
  hf.of_isPullback g _ (fun i ↦ Limits.pullback.snd g (f i)) fun i ↦ .of_hasPullback g (f i)

/-- Nisnevich coverings are stable under composition: refining each member of a Nisnevich
covering by a Nisnevich covering gives a Nisnevich covering. -/
theorem comp (hf : IsNisnevichCovering f) {σ : ι → Type*} {Y : ∀ i, σ i → Scheme.{u}}
    {g : ∀ i j, Y i j ⟶ X i} (hg : ∀ i, IsNisnevichCovering (g i)) :
    IsNisnevichCovering (fun p : Σ i, σ i ↦ g p.1 p.2 ≫ f p.1) where
  etale p := have := hf.etale p.1; have := (hg p.1).etale p.2; inferInstance
  exists_isIso s := by
    obtain ⟨i, x, rfl, hx⟩ := hf.exists_isIso s
    obtain ⟨j, y, rfl, hy⟩ := (hg i).exists_isIso x
    refine ⟨⟨i, j⟩, y, rfl, ?_⟩
    dsimp only
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hx hy

end IsNisnevichCovering

/-- A single isomorphism is a Nisnevich covering. -/
theorem isNisnevichCovering_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsNisnevichCovering (fun _ : PUnit.{1} ↦ f) where
  etale _ := inferInstance
  exists_isIso y := ⟨.unit, inv f y, by simp [← Scheme.Hom.comp_apply], inferInstance⟩

/-- **Zariski coverings are Nisnevich coverings**: a jointly surjective family of open
immersions is a Nisnevich covering, since open immersions are étale and preserve residue
fields. -/
theorem isNisnevichCovering_of_zariski {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (hf : Presieve.ofArrows X f ∈ AlgebraicGeometry.Scheme.zariskiPrecoverage S) :
    IsNisnevichCovering f := by
  rw [AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff] at hf
  refine ⟨fun i ↦ have := hf.2 i; inferInstance, fun s ↦ ?_⟩
  obtain ⟨i, x, hx⟩ := hf.1 s
  have := hf.2 i
  exact ⟨i, x, hx, inferInstance⟩

/-- The Nisnevich precoverage on the category of schemes: a presieve on `S` is covering if its
morphisms are étale and every point of `S` has a preimage under one of them with the same
residue field. -/
def nisnevichPrecoverage : Precoverage Scheme.{u} where
  coverings S := {R | (∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ S), R g → Etale g) ∧
    ∀ s : S, ∃ (Y : Scheme.{u}) (g : Y ⟶ S), R g ∧ ∃ y : Y, g y = s ∧ IsIso (g.residueFieldMap y)}

/-- A presieve on `S` is a Nisnevich covering presieve exactly when its morphisms are étale and
every point of `S` has a preimage under one of them with the same residue field. -/
theorem mem_nisnevichPrecoverage_iff {R : Presieve S} :
    R ∈ nisnevichPrecoverage S ↔ (∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ S), R g → Etale g) ∧
      ∀ s : S, ∃ (Y : Scheme.{u}) (g : Y ⟶ S), R g ∧ ∃ y : Y, g y = s ∧
        IsIso (g.residueFieldMap y) :=
  Iff.rfl

/-- A family of morphisms generates a covering presieve of the Nisnevich precoverage exactly
when it is a Nisnevich covering. -/
@[simp]
theorem ofArrows_mem_nisnevichPrecoverage_iff {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} :
    Presieve.ofArrows X f ∈ nisnevichPrecoverage S ↔ IsNisnevichCovering f := by
  rw [mem_nisnevichPrecoverage_iff]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun i ↦ h₁ _ (.mk i), fun s ↦ ?_⟩, fun hf ↦ ⟨?_, fun s ↦ ?_⟩⟩
  · obtain ⟨Y, g, ⟨i⟩, y, hy, hiso⟩ := h₂ s
    exact ⟨i, y, hy, hiso⟩
  · rintro _ _ ⟨i⟩
    exact hf.etale i
  · obtain ⟨i, x, hx, hiso⟩ := hf.exists_isIso s
    exact ⟨_, _, .mk i, x, hx, hiso⟩

instance : nisnevichPrecoverage.{u}.HasIsos where
  mem_coverings_of_isIso f _ := by
    rw [← Presieve.ofArrows_pUnit.{0}, ofArrows_mem_nisnevichPrecoverage_iff]
    exact isNisnevichCovering_of_isIso f

instance : nisnevichPrecoverage.{u}.IsStableUnderBaseChange where
  mem_coverings_of_isPullback := by
    intro _ _ _ f hf _ g _ p₁ p₂ h
    rw [ofArrows_mem_nisnevichPrecoverage_iff] at hf ⊢
    exact hf.of_isPullback g p₁ p₂ h

instance : nisnevichPrecoverage.{u}.IsStableUnderComposition where
  comp_mem_coverings := by
    intro _ _ _ f hf _ _ g hg
    rw [ofArrows_mem_nisnevichPrecoverage_iff] at hf ⊢
    exact hf.comp fun i ↦ ofArrows_mem_nisnevichPrecoverage_iff.mp (hg i)

/-- Every Nisnevich covering is an étale covering. -/
theorem nisnevichPrecoverage_le_etalePrecoverage :
    nisnevichPrecoverage.{u} ≤ AlgebraicGeometry.Scheme.etalePrecoverage := by
  intro S R hR
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_nisnevichPrecoverage_iff] at hR
  exact (AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr
    ⟨fun s ↦ (hR.exists_eq s).imp fun _ ⟨x, hx⟩ ↦ ⟨x, hx⟩, hR.etale⟩

/-- Every Zariski covering is a Nisnevich covering. -/
theorem zariskiPrecoverage_le_nisnevichPrecoverage :
    AlgebraicGeometry.Scheme.zariskiPrecoverage.{u} ≤ nisnevichPrecoverage := by
  intro S R hR
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  exact ofArrows_mem_nisnevichPrecoverage_iff.mpr (isNisnevichCovering_of_zariski hR)

/-- The big Nisnevich topology on the category of schemes, generated by the Nisnevich
precoverage. -/
abbrev nisnevichTopology : GrothendieckTopology Scheme.{u} :=
  nisnevichPrecoverage.toGrothendieck

/-- A sieve is a Nisnevich covering sieve exactly when it contains a Nisnevich covering
presieve. -/
theorem mem_nisnevichTopology_iff {S : Scheme.{u}} {R : Sieve S} :
    R ∈ nisnevichTopology S ↔ ∃ T ∈ nisnevichPrecoverage S, T ≤ R :=
  Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition

/-- The Nisnevich topology is finer than the Zariski topology. -/
theorem zariskiTopology_le_nisnevichTopology :
    AlgebraicGeometry.Scheme.zariskiTopology.{u} ≤ nisnevichTopology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_nisnevichPrecoverage

/-- The Nisnevich topology is coarser than the étale topology. -/
theorem nisnevichTopology_le_etaleTopology :
    nisnevichTopology.{u} ≤ AlgebraicGeometry.Scheme.etaleTopology :=
  Precoverage.toGrothendieck_mono nisnevichPrecoverage_le_etalePrecoverage

/-- The Nisnevich topology is subcanonical: it is coarser than the subcanonical pro-étale
topology. -/
instance nisnevichTopology_subcanonical : nisnevichTopology.{u}.Subcanonical :=
  .of_le (nisnevichTopology_le_etaleTopology.trans
    AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology)

end MathlibExt.NisSource.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

open MathlibExt.NisSource.AlgebraicGeometry.Scheme

/-- The small Nisnevich site of a scheme `X`: the topology on the category `X.Etale` of schemes
étale over `X` induced from the big Nisnevich topology. -/
def smallNisnevichTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  (Scheme.Etale.forget X).restrictedTopology (nisnevichTopology.over X)

/-- The small Nisnevich topology is generated by the presieves whose underlying morphisms of
schemes form a Nisnevich covering. -/
theorem smallNisnevichTopology_eq_toGrothendieck (X : Scheme.{u}) :
    X.smallNisnevichTopology = (nisnevichPrecoverage.comap
      (Scheme.Etale.forget X ⋙ Over.forget X)).toGrothendieck :=
  have : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  (MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology _
    (nisnevichPrecoverage_le_etalePrecoverage.trans inf_le_right)).symm

/-- A family of morphisms in `X.Etale` generates a covering sieve of the small Nisnevich site
exactly when the underlying morphisms of schemes form a Nisnevich covering. -/
theorem ofArrows_mem_smallNisnevichTopology_iff {X : Scheme.{u}} {W : X.Etale} {ι : Type*}
    {Z : ι → X.Etale} (f : ∀ i, Z i ⟶ W) :
    Sieve.ofArrows Z f ∈ X.smallNisnevichTopology W ↔
      IsNisnevichCovering (fun i ↦ (f i).left) := by
  refine ⟨fun h ↦ ?_, fun hf ↦ ?_⟩
  · have hcp : CoverPreserving X.smallNisnevichTopology (nisnevichTopology.over X)
        (Scheme.Etale.forget X) := by
      have : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale :=
        MorphismProperty.IsMultiplicative.toIsStableUnderComposition
      rw [smallNisnevichTopology_eq_toGrothendieck]
      exact MorphismProperty.coverPreserving_comap_forget _
        (nisnevichPrecoverage_le_etalePrecoverage.trans inf_le_right)
    have h' := hcp.cover_preserve h
    rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_ofArrows, mem_nisnevichTopology_iff] at h'
    obtain ⟨T, hT, hle⟩ := h'
    refine ⟨fun i ↦ inferInstance, fun s ↦ ?_⟩
    obtain ⟨Y, g, hg, y, rfl, hiso⟩ := (mem_nisnevichPrecoverage_iff.mp hT).2 s
    obtain ⟨V, k, _, ⟨i⟩, rfl⟩ := hle _ g hg
    exact ⟨i, k y, rfl, @Hom.isIso_residueFieldMap_of_comp _ _ _ k _ y hiso⟩
  · rw [smallNisnevichTopology_eq_toGrothendieck]
    apply Precoverage.generate_mem_toGrothendieck
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact ofArrows_mem_nisnevichPrecoverage_iff.mpr hf

/-- A sieve on `W` in `X.Etale` is a covering sieve of the small Nisnevich site exactly when it
contains a family whose underlying morphisms of schemes form a Nisnevich covering. -/
theorem mem_smallNisnevichTopology_iff {X : Scheme.{u}} {W : X.Etale} {R : Sieve W} :
    R ∈ X.smallNisnevichTopology W ↔ ∃ (ι : Type (u + 1)) (Z : ι → X.Etale) (f : ∀ i, Z i ⟶ W),
      IsNisnevichCovering (fun i ↦ (f i).left) ∧ Sieve.ofArrows Z f ≤ R := by
  refine ⟨fun hR ↦ ?_, fun ⟨ι, Z, f, hf, hle⟩ ↦ ?_⟩
  · obtain ⟨ι, Z, f, hR'⟩ := R.arrows.exists_eq_ofArrows
    refine ⟨ι, Z, f, (ofArrows_mem_smallNisnevichTopology_iff f).mp ?_, ?_⟩
    · rwa [Sieve.ofArrows, ← hR', Sieve.generate_sieve]
    · rw [Sieve.ofArrows, ← hR', Sieve.generate_sieve]
  · exact GrothendieckTopology.superset_covering _ hle
      ((ofArrows_mem_smallNisnevichTopology_iff f).mpr hf)

/-- The small Nisnevich topology is coarser than the small étale topology. -/
theorem smallNisnevichTopology_le_smallEtaleTopology (X : Scheme.{u}) :
    X.smallNisnevichTopology ≤ X.smallEtaleTopology := by
  dsimp only [smallNisnevichTopology, smallEtaleTopology, Functor.restrictedTopology]
  exact Precoverage.toGrothendieck_mono <| Precoverage.comap_monotone <|
    GrothendieckTopology.toPrecoverage_monotone fun _ _ hR ↦
      nisnevichTopology_le_etaleTopology _ hR

end AlgebraicGeometry.Scheme
