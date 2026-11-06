/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A genuine homomorphism from the existing extraspecial group into the original source group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoNormalMultiplication

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The canonical central source embedding is faithful. -/
theorem co1UniversalCentralEmbedding_injective
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    Function.Injective (co1UniversalCentralEmbedding hfinite hcard hne) := by
  intro a b h
  apply (co1UniversalCommutatorEquiv hfinite hcard hne).symm.injective
  exact Subtype.ext h

/-- The exact natural source binary quotient kills the entire canonical central embedding. -/
theorem co1UniversalCentralEmbedding_binary
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (a : Multiplicative (ZMod 2)) :
    co1UniversalIntoBinary (co1UniversalCentralEmbedding hfinite hcard hne a) = 1 := by
  have h : co1UniversalCentralEmbedding hfinite hcard hne a ∈
      commutator Co1UniversalPresentation :=
    ((co1UniversalCommutatorEquiv hfinite hcard hne).symm a).property
  rw [← co1UniversalIntoBinary_ker] at h
  exact h

/-- The existing extraspecial cocycle group maps by exact central and ordered block source words. -/
def co1UniversalQHom
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) : Q →* Co1UniversalPresentation where
  toFun x := co1UniversalCentralEmbedding hfinite hcard hne x.coeff *
    co1UniversalNormalLift hfinite hcard hne x.base.toAdd
  map_one' := by
    change co1UniversalCentralEmbedding hfinite hcard hne 1 *
      co1UniversalNormalLift hfinite hcard hne 0 = 1
    rw [map_one, co1UniversalNormalLift_zero, one_mul]
  map_mul' x y := by
    let Z := co1UniversalCentralEmbedding hfinite hcard hne
    let N := co1UniversalNormalLift hfinite hcard hne
    have hc : Z y.coeff * N x.base.toAdd = N x.base.toAdd * Z y.coeff :=
      (Subgroup.mem_center_iff.mp
        (co1UniversalCentralEmbedding_mem_center hfinite hcard hne y.coeff) _).symm
    change Z (x.coeff * y.coeff * Multiplicative.ofAdd (qBeta x.base.toAdd y.base.toAdd)) *
      N (x.base.toAdd + y.base.toAdd) =
        (Z x.coeff * N x.base.toAdd) * (Z y.coeff * N y.base.toAdd)
    calc
      _ = (Z x.coeff * Z y.coeff) *
          (Z (Multiplicative.ofAdd (qBeta x.base.toAdd y.base.toAdd)) *
            N (x.base.toAdd + y.base.toAdd)) := by
        rw [map_mul, map_mul]
        simp only [mul_assoc]
      _ = (Z x.coeff * Z y.coeff) * (N x.base.toAdd * N y.base.toAdd) := by
        rw [← co1UniversalNormalLift_mul hfinite hcard hne]
      _ = Z x.coeff * ((Z y.coeff * N x.base.toAdd) * N y.base.toAdd) := by
        simp only [mul_assoc]
      _ = Z x.coeff * ((N x.base.toAdd * Z y.coeff) * N y.base.toAdd) := by rw [hc]
      _ = (Z x.coeff * N x.base.toAdd) * (Z y.coeff * N y.base.toAdd) := by
        simp only [mul_assoc]

/-- The extraspecial-to-source map retains the exact natural binary quotient. -/
theorem co1UniversalQHom_binary
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (x : Q) :
    co1UniversalIntoBinary (co1UniversalQHom hfinite hcard hne x) = qQuotHom x := by
  change co1UniversalIntoBinary
    (co1UniversalCentralEmbedding hfinite hcard hne x.coeff *
      co1UniversalNormalLift hfinite hcard hne x.base.toAdd) = x.base
  rw [map_mul, co1UniversalCentralEmbedding_binary, one_mul, co1UniversalNormalLift_image]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
