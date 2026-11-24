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
# Homology of the positive-index restriction when the boundary into zero vanishes

The positive restriction retains the original incoming differential in every
degree. At its boundary degree zero, native cokernel homology identifies it
with the original degree-one homology when the original d₁ is zero. Above zero,
the native embedding-restriction homology isomorphism applies directly.
The same original quotient class therefore carries the n to n + 1 shift.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : ChainComplex C ℕ)

/-- The native degree-zero cokernel is also the original degree-one homology
when the original outgoing degree-one differential vanishes. -/
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

/-- The positive restriction homology in every higher degree is the original homology one degree up. -/
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

/-- For a complex with zero original d₁, positive restriction gives the actual
n to n + 1 homology shift in all degrees. -/
def positiveRestrictionHomologyIso (h : K.d 1 0 = 0) : ∀ n : ℕ,
    (K.restriction ComplexShape.positiveNatEmbedding).homology n ≅ K.homology (n + 1)
  | 0 => positiveRestrictionHomologyZeroIso K h
  | n + 1 => positiveRestrictionHomologySuccIso K n

end ChainComplex
