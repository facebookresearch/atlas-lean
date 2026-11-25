/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.CompStructCompat
public import MathlibExt.AlgebraicTopology.SimplicialSet.HornOpposite
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv

/-!
# Opposite equivalence edges and inner fibrations

Inverse data transports through `op` and `unop`, with the two composition
witnesses swapping roles.  Consequently equivalence edges transport in both
directions.  The opposite of an inner fibration is an inner fibration, proved
by reversing every inner-horn lifting problem through the Arrow isomorphism
from `SSet.horn.opArrowIso`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

namespace Edge

variable {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}

/-- Reversal fixes `0` in `Fin 1`. -/
private lemma rev_zero_one : (0 : Fin 1).rev = 0 := rfl

/-- The opposite of an identity edge is the identity edge. -/
@[simp]
lemma op_id (x : X _⦋0⦌) : (Edge.id x).op = Edge.id (opObjEquiv.symm x) := by
  refine Edge.ext ?_
  rw [Edge.op_edge, Edge.id_edge, Edge.id_edge, op_σ, rev_zero_one,
    Equiv.apply_symm_apply]

/-- The un-opposite of an identity edge is the identity edge. -/
@[simp]
lemma unop_id {x : X.op _⦋0⦌} :
    (Edge.id x).unop = Edge.id (opObjEquiv x) := by
  refine Edge.ext ?_
  rw [Edge.unop_edge, Edge.id_edge, Edge.id_edge]
  have h : opObjEquiv (X.op.σ (0 : Fin 1) x) =
      opObjEquiv (X.op.σ (0 : Fin 1).rev x) := by rw [rev_zero_one]
  exact h.trans (σ_opObjEquiv X 0 x).symm

/-- Inverse data transports to the opposite: the two composition
witnesses swap roles, since opposite composition reverses order. -/
def InvStruct.op {e : Edge x₀ x₁} (I : e.InvStruct) : (e.op).InvStruct where
  inv := I.inv.op
  homInvId := (I.invHomId.op).ofEq rfl rfl
    (congrArg Edge.edge (Edge.op_id x₁))
  invHomId := (I.homInvId.op).ofEq rfl rfl
    (congrArg Edge.edge (Edge.op_id x₀))

/-- Inverse data transports back from the opposite. -/
def InvStruct.unop {x₀ x₁ : X.op _⦋0⦌} {e : Edge x₀ x₁}
    (I : e.InvStruct) : (e.unop).InvStruct where
  inv := I.inv.unop
  homInvId := (I.invHomId.unop).ofEq rfl rfl
    (congrArg Edge.edge (Edge.unop_id (x := x₁)))
  invHomId := (I.homInvId.unop).ofEq rfl rfl
    (congrArg Edge.edge (Edge.unop_id (x := x₀)))

/-- An equivalence edge has an opposite equivalence edge. Only the
source quasicategory hypothesis is needed. -/
theorem IsEquivalence.op [Quasicategory X] {e : Edge x₀ x₁}
    (h : e.IsEquivalence) : e.op.IsEquivalence :=
  InvStruct.isEquivalence h.nonempty_invStruct.some.op

/-- An equivalence edge in the opposite comes from an equivalence
edge. Only the opposite quasicategory hypothesis is needed. -/
theorem IsEquivalence.unop [Quasicategory X.op] {x₀ x₁ : X.op _⦋0⦌}
    {e : Edge x₀ x₁} (h : e.IsEquivalence) : e.unop.IsEquivalence :=
  InvStruct.isEquivalence h.nonempty_invStruct.some.unop

end Edge
section InnerFibrationOp

/-- The opposite of an inner fibration is an inner fibration. A
lifting problem against `Λ[n+2, j].ι` in the op-world is, via the
op-equivalence, one against `op(Λ[n+2, j].ι)` and `op(op q)`;
`hornOppositeIso` and `stdSimplex.opIso` identify the left arrow
with `Λ[n+2, j.rev].ι` (still inner), and the counit identifies the
right arrow with `q`. -/
theorem InnerFibration.op {X Y : SSet.{u}} {q : X ⟶ Y}
    [InnerFibration q] : InnerFibration (opFunctor.map q) := by
  rw [innerFibration_iff]
  refine fun A B i hi ↦ ?_
  match hi with
  | SSet.innerHornInclusions.intro j h0 hn =>
    rename_i n
    have h0' : 0 < j.rev := by
      rw [Fin.lt_def] at hn ⊢
      simp only [Fin.val_rev, Fin.val_last, Fin.val_zero] at hn ⊢
      omega
    have hn' : j.rev < Fin.last (n + 2) := by
      rw [Fin.lt_def] at h0 ⊢
      simp only [Fin.val_rev, Fin.val_last, Fin.val_zero] at h0 ⊢
      omega
    have hbase : HasLiftingProperty Λ[n + 2, j.rev].ι q :=
      mem_innerFibrations q _
        (SSet.horn_ι_mem_innerHornInclusions h0' hn')
    rw [← Functor.hasLiftingProperty_iff_of_isEquivalence
      SSet.opEquivalence.functor]
    change HasLiftingProperty (opFunctor.map Λ[n + 2, j].ι)
      (opFunctor.map (opFunctor.map q))
    have eL : Arrow.mk (opFunctor.map Λ[n + 2, j].ι) ≅
        Arrow.mk Λ[n + 2, j.rev].ι :=
      horn.opArrowIso (n + 2) j
    have eR : Arrow.mk (opFunctor.map (opFunctor.map q)) ≅ Arrow.mk q :=
      Arrow.isoMk (SSet.opEquivalence.counitIso.app X)
        (SSet.opEquivalence.counitIso.app Y)
        (SSet.opEquivalence.counitIso.hom.naturality q).symm
    have h1 : HasLiftingProperty (opFunctor.map Λ[n + 2, j].ι) q :=
      HasLiftingProperty.of_arrow_iso_left eL.symm q
    exact HasLiftingProperty.of_arrow_iso_right
      (opFunctor.map Λ[n + 2, j].ι) eR.symm

end InnerFibrationOp
end SSet
