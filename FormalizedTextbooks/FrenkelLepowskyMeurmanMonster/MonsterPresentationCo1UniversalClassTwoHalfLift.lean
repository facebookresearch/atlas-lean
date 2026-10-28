/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The two actual binary coordinate blocks lift homomorphically into the original source group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoBasisHom

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A source lift of an entire actual hyperbolic coordinate block, using commuting bit lifts. -/
def co1UniversalHalfLift
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (b : Fin 2) :
    Multiplicative (Fin 12 → ZMod 2) →* Co1UniversalPresentation where
  toFun v := Finset.univ.noncommProd
    (fun i => co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b i)
      (Multiplicative.ofAdd (v.toAdd i)))
    (fun i _ j _ _ => co1UniversalBasisHom_half_commute hfinite hcard hne b i j _ _)
  map_one' := by
    change Finset.univ.noncommProd (fun i =>
      co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b i) 1) _ = 1
    exact (Finset.noncommProd_eq_pow_card Finset.univ _ _ 1
      (fun i _ => map_one _)).trans (one_pow _)
  map_mul' v w := by
    let f := fun i => co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b i)
      (Multiplicative.ofAdd (v.toAdd i))
    let g := fun i => co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b i)
      (Multiplicative.ofAdd (w.toAdd i))
    have hf : ((Finset.univ : Finset (Fin 12)) : Set (Fin 12)).Pairwise
        (fun i j => Commute (f i) (f j)) :=
      fun i _ j _ _ => co1UniversalBasisHom_half_commute hfinite hcard hne b i j _ _
    have hg : ((Finset.univ : Finset (Fin 12)) : Set (Fin 12)).Pairwise
        (fun i j => Commute (g i) (g j)) :=
      fun i _ j _ _ => co1UniversalBasisHom_half_commute hfinite hcard hne b i j _ _
    have hgf : ((Finset.univ : Finset (Fin 12)) : Set (Fin 12)).Pairwise
        (fun i j => Commute (g i) (f j)) :=
      fun i _ j _ _ => co1UniversalBasisHom_half_commute hfinite hcard hne b i j _ _
    have he : ∀ i ∈ (Finset.univ : Finset (Fin 12)),
        co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b i)
          (Multiplicative.ofAdd ((v * w).toAdd i)) = (f * g) i := by
      intro i _
      exact map_mul (co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b i))
        (Multiplicative.ofAdd (v.toAdd i)) (Multiplicative.ofAdd (w.toAdd i))
    exact (Finset.noncommProd_congr rfl he _).trans
      (Finset.noncommProd_mul_distrib f g hf hg hgf)

/-- The block homomorphism evaluates as the finite product of its commuting actual bit lifts. -/
theorem co1UniversalHalfLift_apply
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (b : Fin 2)
    (v : Multiplicative (Fin 12 → ZMod 2)) :
    co1UniversalHalfLift hfinite hcard hne b v = Finset.univ.noncommProd
      (fun i => co1UniversalBasisHom hfinite hcard hne (co1UniversalHalfIndex b i)
        (Multiplicative.ofAdd (v.toAdd i)))
      (fun i _ j _ _ => co1UniversalBasisHom_half_commute hfinite hcard hne b i j _ _) := rfl

/-- The actual binary coordinate vector of a selected hyperbolic half-block. -/
def co1UniversalHalfVector (b : Fin 2) (v : Fin 12 → ZMod 2) : Fin 24 → ZMod 2 :=
  ∑ i : Fin 12, Pi.single (co1UniversalHalfIndex b i) (v i)

/-- The homomorphic source block lift retains every actual binary coordinate. -/
theorem co1UniversalHalfLift_image
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (b : Fin 2)
    (v : Multiplicative (Fin 12 → ZMod 2)) :
    co1UniversalIntoBinary (co1UniversalHalfLift hfinite hcard hne b v) =
      Multiplicative.ofAdd (co1UniversalHalfVector b v.toAdd) := by
  rw [co1UniversalHalfLift_apply, Finset.map_noncommProd]
  simp only [co1UniversalBasisHom_image hfinite hcard hne]
  rw [Finset.noncommProd_eq_prod]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
