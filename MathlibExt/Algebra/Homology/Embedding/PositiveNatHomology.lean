/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.PositiveNat
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Homology of a positive chain restriction

Restrict a nonnegative chain complex by n↦n+1. In every positive
restricted degree, homology is the original homology one degree higher.
At restricted degree zero this identification requires the original
outgoing differential d_1 : K_1→K_0 to vanish.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : ChainComplex C ℕ)

/--
Let K be a nonnegative chain complex in an abelian category C and let e(n)=n+1 be the
positive-degree embedding. If K.d 1 0 = 0, then H₀(K.restriction e) ≅ H₁(K). The condition
makes all of K₁ cycles; the restricted degree-zero homology is the cokernel of the original
incoming differential K₂→K₁.
-/
def positiveRestrictionHomologyZeroIso (h : K.d 1 0 = 0) :
    (K.restriction ComplexShape.positiveNatEmbedding).homology 0 ≅ K.homology 1 := by
  let P := K.restriction ComplexShape.positiveNatEmbedding
  let S := K.sc' 2 1 0
  have hprev : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)
  have hnext : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
  let e := K.homologyIsoSc' 2 1 0 hprev hnext
  have hg : S.g = 0 := h
  let c : CokernelCofork S.f := CokernelCofork.ofπ (homologyZeroClass P)
    (d_comp_homologyZeroClass P)
  let hc : IsColimit c := by
    exact homologyZeroCoforkIsColimit P
  let hl : S.LeftHomologyData := ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork S hg c hc
  exact hl.homologyIso.symm ≪≫ e.symm

/--
Let K be a nonnegative chain complex in an abelian category C and let e(n)=n+1 be the
positive-degree embedding. For every n∈ℕ, H_{n+1}(K.restriction e) ≅ H_{n+2}(K). These degrees
retain both adjacent differentials of K, so no condition on K.d 1 0 is required.
-/
def positiveRestrictionHomologySuccIso (n : ℕ) :
    (K.restriction ComplexShape.positiveNatEmbedding).homology (n + 1) ≅ K.homology (n + 2) :=
  K.restrictionHomologyIso ComplexShape.positiveNatEmbedding
    (n + 2) (n + 1) n
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl))
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))
    (show ComplexShape.positiveNatEmbedding.f (n + 2) = n + 3 from rfl)
    (show ComplexShape.positiveNatEmbedding.f (n + 1) = n + 2 from rfl)
    (show ComplexShape.positiveNatEmbedding.f n = n + 1 from rfl)
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 3) (n + 2) from rfl))
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl))

/--
Let K be a nonnegative chain complex in an abelian category C and let e(n)=n+1 be the
positive-degree embedding. If K.d 1 0 = 0, the positive restriction shifts all homology
degrees by one: Hₙ(K.restriction e) ≅ H_{n+1}(K) for every n∈ℕ, including n=0.
-/
def positiveRestrictionHomologyIso (h : K.d 1 0 = 0) : ∀ n : ℕ,
    (K.restriction ComplexShape.positiveNatEmbedding).homology n ≅ K.homology (n + 1)
  | 0 => positiveRestrictionHomologyZeroIso K h
  | n + 1 => positiveRestrictionHomologySuccIso K n

end ChainComplex
