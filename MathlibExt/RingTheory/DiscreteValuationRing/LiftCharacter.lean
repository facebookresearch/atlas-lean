/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Lifting a character of a split finite free algebra over a discrete valuation ring

Let `O` be a discrete valuation ring with residue field `k` and field of fractions `K`, and let `H`
be a commutative `O`-algebra, free of finite rank as an `O`-module, such that every maximal ideal
of `K ⊗[O] H` has residue field `K`. Then every homomorphism of `O`-algebras `χ : H → k` lifts to
a homomorphism of `O`-algebras `χ' : H → O` (`IsDiscreteValuationRing.exists_algHom_residue_eq`).

## Proof

As in Deligne–Serre's proof of their Lemme 6.11: the kernel of `χ` is a maximal ideal of `H`;
let `𝔭 ⊆ Ker χ` be a minimal prime of the noetherian ring `H`. Minimal primes are associated
primes (`Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`), so `𝔭` is the
annihilator of a nonzero element of `H`, and since `H` is free over `O`, `𝔭 ∩ O = 0`. The
homomorphism `K ⊗ H → Frac(H/𝔭)`, `c ⊗ h ↦ c · h̄`, has a prime, hence maximal, kernel in the
artinian ring `K ⊗ H`, so by hypothesis every `h̄` lies in `K`; being integral over `O`, it lies in
`O`, which is integrally closed. So `O → H/𝔭` is an isomorphism, and `χ'` is `H → H/𝔭 ≅ O`; as
`χ` vanishes on `𝔭`, the reduction of `χ'` modulo the maximal ideal of `O` is `χ`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530: proof of Lemme 6.11, p. 522 ("Puisque ℋ est libre sur 𝔒, il existe un idéal
  premier 𝔭 de ℋ contenu dans l'idéal maximal Ker (χ) et tel que 𝔭 ∩ 𝔒 = 0; c'est le noyau d'un
  homomorphisme χ′ : ℋ → 𝔒 dont la réduction mod 𝔪 est χ").
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

/-- **Lifting a character of a split finite free algebra over a discrete valuation ring.** Let
$\mathcal{O}$ be a discrete valuation ring with maximal ideal $\mathfrak{m}$, residue field $k$ and
field of fractions $K$, and let $\mathcal{H}$ be a commutative $\mathcal{O}$-algebra that is free of
finite rank as an $\mathcal{O}$-module and such that every maximal ideal $Q$ of
$K \otimes_{\mathcal{O}} \mathcal{H}$ has residue field $K$, that is, $K \to
(K \otimes_{\mathcal{O}} \mathcal{H})/Q$ is surjective. Then every homomorphism of
$\mathcal{O}$-algebras $\chi \colon \mathcal{H} \to k$ lifts to a homomorphism of
$\mathcal{O}$-algebras $\chi' \colon \mathcal{H} \to \mathcal{O}$:
$$\chi'(h) \equiv \chi(h) \pmod{\mathfrak{m}} \qquad \text{for every } h \in \mathcal{H}.$$
The kernel $\mathfrak{p}$ of $\chi'$ is a prime ideal of $\mathcal{H}$ contained in
$\operatorname{Ker}(\chi)$ with $\mathfrak{p} \cap \mathcal{O} = 0$. Here $k$ is
`IsLocalRing.ResidueField O`, reduction modulo $\mathfrak{m}$ is `IsLocalRing.residue O`, and
$\mathfrak{p} \cap \mathcal{O}$ is the preimage of $\mathfrak{p}$ under `algebraMap O H`.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, proof of Lemme 6.11, p. 522. -/
theorem IsDiscreteValuationRing.exists_algHom_residue_eq {O H : Type*} (K : Type*) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing H] [Algebra O H] [Module.Free O H] [Module.Finite O H]
    (hsplit : ∀ Q : Ideal (K ⊗[O] H), Q.IsMaximal →
      Function.Surjective (Algebra.ofId K ((K ⊗[O] H) ⧸ Q)))
    (χ : H →ₐ[O] IsLocalRing.ResidueField O) :
    ∃ χ' : H →ₐ[O] O, (∀ h, IsLocalRing.residue O (χ' h) = χ h) ∧ (RingHom.ker χ').IsPrime ∧
      RingHom.ker χ' ≤ RingHom.ker χ ∧ (RingHom.ker χ').comap (algebraMap O H) = ⊥ := by
  have : IsNoetherianRing H := isNoetherian_of_tower O inferInstance
  -- a minimal prime `p ⊆ Ker χ`, which is an associated prime of `H`
  have hχsurj : Function.Surjective χ := fun x => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨algebraMap O H y, by simp [IsLocalRing.ResidueField.algebraMap_eq]⟩
  have hM : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχsurj
  have := hM.isPrime
  obtain ⟨p, hpmin, hple⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal H)) (J := RingHom.ker χ) bot_le
  have hp : p.IsPrime := hpmin.1.1
  have hass : p ∈ associatedPrimes H H := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes H H
    rw [Module.annihilator_eq_bot.2 inferInstance]
    exact hpmin
  obtain ⟨-, x, hx⟩ := isAssociatedPrime_iff.1 hass
  -- `p ∩ O = 0`, as `H` is free over `O`
  have hcomap : p.comap (algebraMap O H) = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    rw [Ideal.mem_comap, hx, Submodule.mem_colon] at hc
    have h1 := hc x (Set.mem_singleton x)
    rw [Submodule.mem_bot, algebraMap_smul] at h1
    rcases smul_eq_zero.1 h1 with h | h
    · exact (Submodule.mem_bot O).2 h
    · exfalso
      apply hp.ne_top
      rw [hx, h]
      exact eq_top_iff.2 fun r _ => by simp [Submodule.mem_colon]
  -- `H / p` is a domain containing `O`; map `K ⊗ H` to its field of fractions
  have hOB : Function.Injective (algebraMap O (H ⧸ p)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hc' : c ∈ p.comap (algebraMap O H) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      simpa [Ideal.Quotient.algebraMap_eq] using hc
    rw [hcomap] at hc'
    simpa using hc'
  have hBL : Function.Injective (algebraMap (H ⧸ p) (FractionRing (H ⧸ p))) :=
    IsFractionRing.injective _ _
  have hOL : Function.Injective (algebraMap O (FractionRing (H ⧸ p))) := by
    rw [IsScalarTower.algebraMap_eq O (H ⧸ p) (FractionRing (H ⧸ p))]
    exact hBL.comp hOB
  let f : K →ₐ[O] FractionRing (H ⧸ p) :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId O (FractionRing (H ⧸ p))) hOL
  let g : H →ₐ[O] FractionRing (H ⧸ p) :=
    (IsScalarTower.toAlgHom O (H ⧸ p) (FractionRing (H ⧸ p))).comp (Ideal.Quotient.mkₐ O p)
  let φ : K ⊗[O] H →ₐ[O] FractionRing (H ⧸ p) :=
    Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hφK : ∀ c : K, φ (algebraMap K (K ⊗[O] H) c) = f c := fun c => by
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
  have hφH : ∀ h : H, φ (1 ⊗ₜ h) = g h := fun h => by simp [φ]
  -- its kernel is a maximal ideal of the artinian ring `K ⊗ H`, with residue field `K`
  have : IsArtinianRing (K ⊗[O] H) := IsArtinianRing.of_finite K (K ⊗[O] H)
  have hQprime : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hQ : (RingHom.ker φ).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have hval : ∀ h : H, ∃ c : K, f c = g h := fun h => by
    obtain ⟨c, hc⟩ := hsplit _ hQ (Ideal.Quotient.mk _ (1 ⊗ₜ h))
    refine ⟨c, ?_⟩
    have hc' : Ideal.Quotient.mk (RingHom.ker φ) (algebraMap K (K ⊗[O] H) c) =
        Ideal.Quotient.mk (RingHom.ker φ) (1 ⊗ₜ h) := by
      rw [← hc]
      rfl
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero, hφK, hφH] at hc'
    exact hc'
  -- `O → H / p` is surjective: the values lie in `K` and are integral over `O`
  have hsurj : Function.Surjective (algebraMap O (H ⧸ p)) := by
    intro b
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, hc⟩ := hval h
    have hint : IsIntegral O (f c) := hc ▸ (Algebra.IsIntegral.isIntegral h).map g
    rw [isIntegral_algHom_iff f f.toRingHom.injective] at hint
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨y, hBL ?_⟩
    rw [AlgHom.commutes] at hc
    rw [← IsScalarTower.algebraMap_apply O (H ⧸ p)]
    simpa [g] using hc
  let e : O ≃ₐ[O] H ⧸ p := AlgEquiv.ofBijective (Algebra.ofId O (H ⧸ p)) ⟨hOB, hsurj⟩
  let χ' : H →ₐ[O] O := (e.symm : H ⧸ p →ₐ[O] O).comp (Ideal.Quotient.mkₐ O p)
  have hcong : ∀ h, h - algebraMap O H (χ' h) ∈ p := fun h => by
    rw [← Ideal.Quotient.eq]
    calc Ideal.Quotient.mk p h = e (e.symm (Ideal.Quotient.mk p h)) :=
          (e.apply_symm_apply _).symm
      _ = Ideal.Quotient.mk p (algebraMap O H (χ' h)) := rfl
  have hres : ∀ h, IsLocalRing.residue O (χ' h) = χ h := fun h => by
    have := hple (hcong h)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.commutes,
      IsLocalRing.ResidueField.algebraMap_eq] at this
    exact this.symm
  refine ⟨χ', hres, RingHom.ker_isPrime χ', fun h hh => ?_, ?_⟩
  · rw [RingHom.mem_ker] at hh ⊢
    rw [← hres, hh, map_zero]
  · refine eq_bot_iff.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hc
    simpa using hc

end
