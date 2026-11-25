/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
ported from `TauCeti/RingTheory/Invariant/Basic.lean` in TauCetiProject/TauCeti at revision
62bbc0596dc3539d488232e4e924a338548ea0a9. Retain only the invariant-extension,
prime-conjugacy and domain-point comparison dependencies needed by the geometric quotient
port. No unresolved result is added.
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.Invariant.Basic

@[expose] public noncomputable section
open Polynomial

namespace TauCeti.Algebra.IsInvariant

/-- The fixed subring is an invariant extension: every fixed element lies in its image. -/
instance (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A] :
    Algebra.IsInvariant (FixedPoints.subring A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

end TauCeti.Algebra.IsInvariant

namespace Ideal

open MulAction
open scoped Pointwise

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

variable (A G) in
/-- **Primes with the same contraction to an invariant ring are conjugate.** If `A → B` is an
invariant extension for a finite group `G`, two primes of `B` with the same contraction to `A`
differ by an element of `G`. Unlike Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`, the
action of `G` need not commute with `A`: the argument runs over the fixed subring of `B`, which
lies in the image of `A` and on which `G` acts trivially. -/
theorem exists_smul_eq_of_under_eq [Finite G] [Algebra.IsInvariant A B G] (R R' : Ideal B)
    [R.IsPrime] [R'.IsPrime] (h : R.under A = R'.under A) : ∃ g : G, R' = g • R := by
  refine Algebra.IsInvariant.exists_smul_of_under_eq (FixedPoints.subring B G) B G R R' ?_
  ext d
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) d.1 d.2
  have := congr(a ∈ $h)
  rw [under_def, under_def, mem_comap, mem_comap, ha] at this
  rw [under_def, under_def, mem_comap, mem_comap]
  exact this.to_iff

section Fibres

variable (Q : Ideal B) [Q.IsPrime] (H : Subgroup G) (C : Type*) [CommRing C] [Algebra C B]
  [Finite H] [Algebra.IsInvariant C B H] [SMulCommClass H C B]


end Fibres

end Ideal

namespace TauCeti.Algebra.IsInvariant

variable (A G : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [Algebra.IsInvariant A B G]
  {K : Type*} [CommRing K] [IsDomain K]

/-- **Points with the same restriction take the same values up to translation.** If two ring maps
`φ ψ : B →+* K` to a domain agree on `A`, then every value `ψ b` is the value of `φ` at some
translate of `b`. -/
theorem exists_apply_eq_apply_smul {φ ψ : B →+* K}
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (b : B) :
    ∃ σ : G, ψ b = φ (σ • b) := by
  cases nonempty_fintype G
  -- `ψ b` is a root of the image under `φ` of the orbit polynomial of `b`.
  obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
  -- The orbit polynomial has coefficients in `A`, so `φ` and `ψ` send it to the same polynomial.
  have hmap : (MulSemiringAction.charpoly G b).map ψ = (MulSemiringAction.charpoly G b).map φ := by
    rw [← hp, coe_mapRingHom, map_map, map_map, h]
  have h0 : ((MulSemiringAction.charpoly G b).map φ).eval (ψ b) = 0 := by
    rw [← hmap, eval_map_apply, MulSemiringAction.eval_charpoly, map_zero]
  simpa [MulSemiringAction.charpoly, Polynomial.map_prod, eval_prod, Finset.prod_eq_zero_iff,
    sub_eq_zero] using h0

/-- Two ring maps from `B` to a domain with the same kernel `Q` that agree on `A` differ by the
action of an element of the decomposition group of `Q`: they induce embeddings of `B ⧸ Q` with
the same image, hence differ by an automorphism of `B ⧸ Q` over `A`, which lifts. -/
private theorem exists_comp_eq_of_ker_eq [SMulCommClass G A B] {f₁ f₂ : B →+* K}
    (h : f₁.comp (algebraMap A B) = f₂.comp (algebraMap A B))
    (hker : RingHom.ker f₁ = RingHom.ker f₂) :
    ∃ k : G, f₁.comp (MulSemiringAction.toRingHom G B k) = f₂ := by
  have := RingHom.ker_isPrime f₂
  set Q := RingHom.ker f₂
  -- The embeddings `ι₁` and `ι₂` of `B ⧸ Q` induced by `f₁` and `f₂` have the same image.
  let ι₁ : B ⧸ Q →+* K := Ideal.Quotient.lift Q f₁ fun b hb ↦ by rwa [← RingHom.mem_ker, hker]
  let ι₂ : B ⧸ Q →+* K := Ideal.Quotient.lift Q f₂ fun b hb ↦ hb
  have hι₁ : Function.Injective ι₁ := (Ideal.injective_lift_iff _).mpr hker
  have hι₂ : Function.Injective ι₂ := (Ideal.injective_lift_iff _).mpr rfl
  have hrange {φ ψ : B →+* K} (hφ : RingHom.ker φ = Q) (hψ : RingHom.ker ψ = Q)
      (hφψ : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) :
      (Ideal.Quotient.lift Q ψ fun b hb ↦ by rwa [← RingHom.mem_ker, hψ]).range ≤
        (Ideal.Quotient.lift Q φ fun b hb ↦ by rwa [← RingHom.mem_ker, hφ]).range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨σ, hσ⟩ := exists_apply_eq_apply_smul A G hφψ b
    exact ⟨Ideal.Quotient.mk Q (σ • b), hσ.symm⟩
  have hrange' : ι₂.range = ι₁.range :=
    le_antisymm (hrange hker rfl h) (hrange rfl hker h.symm)
  -- So `τ = ι₁⁻¹ ∘ ι₂` is an automorphism of `B ⧸ Q` over `A ⧸ Q.under A`.
  let e₁ := RingEquiv.ofBijective ι₁.rangeRestrict
    ⟨fun _ _ hxy ↦ hι₁ congr(Subtype.val $hxy), ι₁.rangeRestrict_surjective⟩
  let e₂ := RingEquiv.ofBijective ι₂.rangeRestrict
    ⟨fun _ _ hxy ↦ hι₂ congr(Subtype.val $hxy), ι₂.rangeRestrict_surjective⟩
  let τ : (B ⧸ Q) ≃+* (B ⧸ Q) := (e₂.trans (RingEquiv.subringCongr hrange')).trans e₁.symm
  have hτ (y : B ⧸ Q) : ι₁ (τ y) = ι₂ y :=
    congr(Subtype.val $(e₁.apply_symm_apply (RingEquiv.subringCongr hrange' (e₂ y))))
  let τ' : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := τ) fun a ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hι₁ ((hτ _).trans congr($h a).symm)
  -- Lift `τ` to the decomposition group of `Q`.
  obtain ⟨k, hk⟩ := Ideal.Quotient.stabilizerHom_surjective G (Q.under A) Q τ'
  refine ⟨k, RingHom.ext fun b ↦ ?_⟩
  have := congr(ι₁ ($hk (Ideal.Quotient.mk Q b)))
  rw [Ideal.Quotient.stabilizerHom_apply] at this
  -- `τ'` applies `τ`, and the action of `k` is that of its image in `G`.
  have key : ι₂ (Ideal.Quotient.mk Q b) = ι₁ (Ideal.Quotient.mk Q ((k : G) • b)) :=
    (hτ _).symm.trans this.symm
  simp only [ι₁, Ideal.Quotient.lift_mk] at key
  -- `simp` does not rewrite `ι₂` on `Ideal.Quotient.mk` through its unfolded proof argument.
  simpa using key.symm.trans (Ideal.Quotient.lift_mk _ _ _)

/-- **Points of an invariant extension with the same restriction are conjugate.** Two ring maps
from `B` to a domain that agree on `A` differ by the action of an element of `G`. -/
theorem exists_comp_eq_of_comp_algebraMap_eq (f₁ f₂ : B →+* K)
    (h : f₁.comp (algebraMap A B) = f₂.comp (algebraMap A B)) :
    ∃ g : G, f₁.comp (MulSemiringAction.toRingHom G B g) = f₂ := by
  have := RingHom.ker_isPrime f₁
  have := RingHom.ker_isPrime f₂
  have hunder : (RingHom.ker f₁).under A = (RingHom.ker f₂).under A := by
    ext a
    simp only [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, h]
  -- The kernels are primes above the same prime of `A`, hence conjugate.
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_under_eq A G _ _ hunder
  -- The fixed subring `Bᴳ` lies in the image of `A`, and `G` commutes with it, so the translate
  -- `f₁ ∘ (g⁻¹ • ·)` agrees with `f₂` on `Bᴳ`.
  have h' : (f₁.comp (MulSemiringAction.toRingHom G B g⁻¹)).comp
      (algebraMap (FixedPoints.subring B G) B) =
      f₂.comp (algebraMap (FixedPoints.subring B G) B) := by
    ext d
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) d.1 d.2
    have := congr($h a)
    simp only [RingHom.comp_apply, ha] at this
    simpa [d.2 g⁻¹, Algebra.algebraMap_ofSubsemiring_apply] using this
  have hker : RingHom.ker (f₁.comp (MulSemiringAction.toRingHom G B g⁻¹)) = RingHom.ker f₂ := by
    rw [hg]
    ext b
    simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  obtain ⟨k, hk⟩ := exists_comp_eq_of_ker_eq (FixedPoints.subring B G) G h' hker
  refine ⟨g⁻¹ * k, RingHom.ext fun b ↦ ?_⟩
  simpa [mul_smul] using congr($hk b)

end TauCeti.Algebra.IsInvariant
