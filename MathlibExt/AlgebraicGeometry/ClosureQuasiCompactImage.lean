/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The closure of the image of a quasi-compact morphism

* `PrimeSpectrum.exists_comap_le_of_ker_le`: for a ring map `φ : R →+* A` and a prime `p` of `R`
  containing `ker φ`, some prime of `A` contracts into `p`.
* `AlgebraicGeometry.Scheme.Hom.exists_specializes_of_mem_closure_range`: for a quasi-compact
  morphism of schemes `f : X ⟶ Y`, every point of the closure of the image of `f` is a
  specialization of a point of the image (Stacks project, Morphisms, Lemma 29.6.5, Tag 02JQ, for
  the closure of the image).

The proof reduces to an affine open `V` of `Y` and a finite affine open covering of `f⁻¹ V`, where
the closure of the image of `Spec A → Spec R` is the zero locus of the kernel of `R → A`
(`PrimeSpectrum.closure_range_comap`).
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- For a ring map `φ : R →+* A` and a prime `p` of `R` containing the kernel of `φ`, there is a
prime `q` of `A` whose contraction `φ⁻¹ q` is contained in `p`. -/
theorem PrimeSpectrum.exists_comap_le_of_ker_le {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (p : PrimeSpectrum R) (hp : RingHom.ker φ ≤ p.asIdeal) :
    ∃ q : PrimeSpectrum A, PrimeSpectrum.comap φ q ≤ p := by
  obtain ⟨q, hq, -, hdisj⟩ :=
    Ideal.exists_le_prime_disjoint (⊥ : Ideal A) (p.asIdeal.primeCompl.map φ) <| by
      rw [Set.disjoint_left]
      rintro _ h0 ⟨x, hx, rfl⟩
      exact hx (hp ((RingHom.mem_ker).2 ((Ideal.mem_bot).1 h0)))
  refine ⟨⟨q, hq⟩, fun x hx ↦ ?_⟩
  by_contra hxp
  exact Set.disjoint_left.1 hdisj hx ⟨x, hxp, rfl⟩

namespace AlgebraicGeometry

/-- **The closure of the image of a quasi-compact morphism.** Let `f : X ⟶ Y` be a quasi-compact
morphism of schemes. Then every point `y` of the closure of the image of `f` is a specialization of
a point of the image: there is `x : X` with `f x ⤳ y`.

This is the closure form of the Stacks project, Morphisms, Lemma 29.6.5 (Tag 02JQ), for a
quasi-compact morphism `f : X → Y` with scheme theoretic image `Z`: "In particular any point of `Z`
is the specialization of a point of `f(X)`." For quasi-compact `f`, the underlying set of `Z` is
the closure of `f(X)` (Morphisms, Lemma 29.6.3, Tag 01R8). -/
theorem Scheme.Hom.exists_specializes_of_mem_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {y : Y} (hy : y ∈ closure (Set.range f)) : ∃ x, f x ⤳ y := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hV : IsAffineOpen V := hV
  obtain ⟨s, hs, hU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := f ⁻¹ᵁ V)).1
    (QuasiCompact.isCompact_preimage (f := f) _ V.isOpen hV.isCompact)
  have hle (i : X.affineOpens) (hi : i ∈ s) : (i : X.Opens) ≤ f ⁻¹ᵁ V := by
    rw [hU]
    exact le_biSup (fun i : X.affineOpens ↦ (i : X.Opens)) hi
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have hsub : hV.fromSpec ⁻¹' Set.range f ⊆
      ⋃ i ∈ s, hV.fromSpec ⁻¹' (f '' ((i : X.Opens) : Set X)) := by
    rintro p' ⟨x, hx⟩
    have hxV : x ∈ f ⁻¹ᵁ V := by
      have h := Set.mem_range_self (f := hV.fromSpec) p'
      rw [hV.range_fromSpec, ← hx] at h
      exact h
    rw [hU] at hxV
    obtain ⟨i, hi, hxi⟩ : ∃ i ∈ s, x ∈ (i : X.Opens) := by simpa using hxV
    exact Set.mem_biUnion hi ⟨x, hxi, hx⟩
  have hp : p ∈ closure (⋃ i ∈ s, hV.fromSpec ⁻¹' (f '' ((i : X.Opens) : Set X))) :=
    closure_mono hsub <| by
      rw [← hV.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
        hV.fromSpec.continuous]
      exact hy
  rw [hs.closure_biUnion] at hp
  obtain ⟨i, hi, hp⟩ := Set.mem_iUnion₂.1 hp
  have hi' : IsAffineOpen (i : X.Opens) := i.2
  let φ := f.appLE V i (hle i hi)
  have hcomm : Spec.map φ ≫ hV.fromSpec = hi'.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hi' (hle i hi)
  have key (q : Spec Γ(X, (i : X.Opens))) : hV.fromSpec (Spec.map φ q) = f (hi'.fromSpec q) := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  have hrange : hV.fromSpec ⁻¹' (f '' ((i : X.Opens) : Set X)) ⊆ Set.range (Spec.map φ) := by
    rintro p' ⟨x, hxi, hx⟩
    obtain ⟨q, rfl⟩ : x ∈ Set.range hi'.fromSpec := by rwa [hi'.range_fromSpec]
    exact ⟨q, hV.fromSpec.isOpenEmbedding.injective ((key q).trans hx)⟩
  have hp' : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker φ.hom) := by
    rw [← PrimeSpectrum.closure_range_comap]
    convert closure_mono hrange hp using 3
    rw [Spec.map_base]
    rfl
  obtain ⟨q, hq⟩ := PrimeSpectrum.exists_comap_le_of_ker_le φ.hom p
    ((PrimeSpectrum.mem_zeroLocus _ _).1 hp')
  let q' : Spec Γ(X, (i : X.Opens)) := q
  refine ⟨hi'.fromSpec q', ?_⟩
  have hq' : Spec.map φ q' ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 hq
  exact key q' ▸ hq'.map hV.fromSpec.continuous

end AlgebraicGeometry
