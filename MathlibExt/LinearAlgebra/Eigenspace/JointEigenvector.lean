/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Colon

/-!
# A character of a commutative algebra of endomorphisms has a joint eigenvector

Let `K` be a field, `V` a finite-dimensional `K`-vector space, `A` a commutative `K`-subalgebra
of `Module.End K V` and `χ : A →ₐ[K] K` a homomorphism of `K`-algebras. Then some nonzero
`v ∈ V` satisfies `a v = χ(a) v` for every `a ∈ A`
(`Module.End.exists_ne_zero_forall_apply_eq_smul_of_algHom`).

## Proof

The kernel `𝔫` of `χ` is a maximal ideal of the finite-dimensional, hence artinian, ring `A`, in
which every prime ideal is maximal. The annihilator of the `A`-module `V` is `0`, so `𝔫` is a
minimal prime over it, and since minimal primes over the annihilator of a finitely generated
module over a noetherian ring are associated primes
(`Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`), `𝔫` is the
annihilator of some `v ∈ V`, which is nonzero since `𝔫 ≠ A`. Each `a - χ(a)` lies in `𝔫` and so
kills `v`.

`Module.End.exists_common_eigenvector_of_commute` gives a common eigenvector over an
algebraically closed field, with eigenvalues it does not prescribe, and
`Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom` prescribes them in characteristic
zero for an action that stabilizes a lattice; the statement here prescribes them through `χ`
over any field.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530: proof of Lemme 6.11, p. 522 ("L'idéal de K ⊗ ℋ engendré par 𝔭 appartient au
  support du module K ⊗ M; on en conclut qu'il existe un élément non nul f″ de K ⊗ M qui est
  annulé par cet idéal, i. e. tel que h f″ = χ′(h) f″ pour tout h ∈ ℋ").
-/

@[expose] public section

set_option autoImplicit false

namespace Module.End

/-- **A character of a commutative algebra of endomorphisms has a joint eigenvector.** Let $K$
be a field, $V$ a finite-dimensional $K$-vector space, $A$ a commutative $K$-subalgebra of
$\operatorname{End}_K(V)$, and $\chi \colon A \to K$ a homomorphism of $K$-algebras. Then there
is a nonzero $v \in V$ with
$$a\, v = \chi(a)\, v \qquad \text{for every } a \in A.$$
The commutativity of $A$ is the hypothesis `hA` that any two elements of $A$ commute.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, proof of Lemme 6.11, p. 522, where $A$ is the image of
$K \otimes_{\mathcal{O}} \mathcal{H}$ in $\operatorname{End}_K(K \otimes_{\mathcal{O}} M)$. -/
theorem exists_ne_zero_forall_apply_eq_smul_of_algHom {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (A : Subalgebra K (Module.End K V))
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (χ : A →ₐ[K] K) :
    ∃ v : V, v ≠ 0 ∧ ∀ a : A, (a : Module.End K V) v = χ a • v := by
  let inst : CommRing A := { (inferInstance : Ring A) with
    mul_comm := fun a b => Subtype.ext (hA a a.2 b b.2) }
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : Module.Finite A V := Module.Finite.of_restrictScalars_finite K A V
  have hsurj : Function.Surjective χ := fun c => ⟨algebraMap K A c, by simp⟩
  have hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hsurj
  have hann : Module.annihilator A V = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    rw [Module.mem_annihilator] at ha
    exact (Submodule.mem_bot A).2 (Subtype.ext (LinearMap.ext fun v => ha v))
  have hmin : RingHom.ker χ ∈ (Module.annihilator A V).minimalPrimes := by
    refine ⟨⟨hmax.isPrime, by rw [hann]; exact bot_le⟩, fun q hq hle => ?_⟩
    have := hq.1
    exact ((IsArtinianRing.isMaximal_of_isPrime q).eq_of_le hmax.ne_top hle).ge
  have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A V hmin
  obtain ⟨-, v, hv⟩ := isAssociatedPrime_iff.1 hass
  refine ⟨v, fun h0 => hmax.ne_top ?_, fun a => ?_⟩
  · rw [hv, h0]
    exact eq_top_iff.2 fun r _ => by simp [Submodule.mem_colon]
  · have hmem : a - algebraMap K A (χ a) ∈ RingHom.ker χ := by simp
    rw [hv, Submodule.mem_colon] at hmem
    have := hmem v (Set.mem_singleton v)
    rw [Submodule.mem_bot, sub_smul, sub_eq_zero] at this
    rw [show (a : Module.End K V) v = a • v from rfl, this, algebraMap_smul]

end Module.End

end
