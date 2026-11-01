/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The existing extraspecial group is isomorphic to the bounded nonabelian source group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoQHom

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The concrete extraspecial-to-source coordinate homomorphism is injective. -/
theorem co1UniversalQHom_injective
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    Function.Injective (co1UniversalQHom hfinite hcard hne) := by
  intro x y h
  have hb := congrArg co1UniversalIntoBinary h
  rw [co1UniversalQHom_binary, co1UniversalQHom_binary] at hb
  change x.base = y.base at hb
  have he : co1UniversalCentralEmbedding hfinite hcard hne x.coeff *
      co1UniversalNormalLift hfinite hcard hne x.base.toAdd =
    co1UniversalCentralEmbedding hfinite hcard hne y.coeff *
      co1UniversalNormalLift hfinite hcard hne y.base.toAdd := h
  rw [hb] at he
  have hc := co1UniversalCentralEmbedding_injective hfinite hcard hne (mul_right_cancel he)
  exact NormalizedCocycleExtension.Extension.ext hb hc

/-- Every source group element is the central coefficient times its literal coordinate section. -/
theorem co1UniversalQHom_surjective
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    Function.Surjective (co1UniversalQHom hfinite hcard hne) := by
  intro x
  let v := (co1UniversalIntoBinary x).toAdd
  let n := co1UniversalNormalLift hfinite hcard hne v
  have hc : x * n⁻¹ ∈ commutator Co1UniversalPresentation := by
    rw [← co1UniversalIntoBinary_ker]
    change co1UniversalIntoBinary (x * n⁻¹) = 1
    rw [map_mul, map_inv, co1UniversalNormalLift_image]
    exact mul_inv_cancel _
  let c : commutator Co1UniversalPresentation := ⟨x * n⁻¹, hc⟩
  refine ⟨⟨Multiplicative.ofAdd v,
    Multiplicative.ofAdd (co1UniversalCommutatorCoefficient c)⟩, ?_⟩
  change co1UniversalCentralEmbedding hfinite hcard hne
    (Multiplicative.ofAdd (co1UniversalCommutatorCoefficient c)) * n = x
  rw [co1UniversalCentralEmbedding_coefficient]
  exact inv_mul_cancel_right x n

/-- The actual extraspecial group and the original source group are isomorphic,
preserving their exact binary coordinates. The source bound and nontriviality are explicit. -/
def co1UniversalQEquiv
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) : Q ≃* Co1UniversalPresentation :=
  MulEquiv.ofBijective (co1UniversalQHom hfinite hcard hne)
    ⟨co1UniversalQHom_injective hfinite hcard hne,
      co1UniversalQHom_surjective hfinite hcard hne⟩

/-- The genuine source isomorphism retains the exact quotient of the existing extraspecial group. -/
theorem co1UniversalQEquiv_binary
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (x : Q) :
    co1UniversalIntoBinary (co1UniversalQEquiv hfinite hcard hne x) = qQuotHom x :=
  co1UniversalQHom_binary hfinite hcard hne x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
