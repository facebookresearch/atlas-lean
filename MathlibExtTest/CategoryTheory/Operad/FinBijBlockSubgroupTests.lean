/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Operad.FinBijBlockSubgroup

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory
open CategoryTheory.Operad CategoryTheory.Operad.SmallFinBijGroupoid

namespace FinBijBlockSubgroupTests

#check @blockMulAction
#check @blockAutHom
#check @blockAutHom_injective
#check @blockAutHom_range_iff
#check @blockIsoEquivAut_smul
#check @blockIsoEquivAut_postcompose
#check @blockMulAction_free
#check @finAutEquiv

private abbrev cardinal (n : ℕ) : SmallFinBijGroupoid := ⟨FintypeCat.Skeleton.mk n⟩

private def cardinalBlockIso {r n q : ℕ} (h : r + n = q) :
    cardinal r ⊗ cardinal n ≅ cardinal q :=
  eqToIso (congrArg cardinal h)

private def sigmaBlockHom {r n q : ℕ} (h : r + n = q) :
    Equiv.Perm (Fin r) →* Equiv.Perm (Fin q) :=
  (finAutEquiv (cardinal q)).toMonoidHom.comp
    ((blockAutHom (cardinal r) (cardinal n) (cardinal q) (cardinalBlockIso h)).comp
      (finAutEquiv (cardinal r)).symm.toMonoidHom)

example (n q : ℕ) (h : n ≤ q) :
    Function.Injective (sigmaBlockHom (Nat.sub_add_cancel h)) := by
  intro a c hac
  change finAutEquiv (cardinal q)
      (blockAutHom (cardinal (q - n)) (cardinal n) (cardinal q)
        (cardinalBlockIso (Nat.sub_add_cancel h)) ((finAutEquiv (cardinal (q - n))).symm a)) =
    finAutEquiv (cardinal q)
      (blockAutHom (cardinal (q - n)) (cardinal n) (cardinal q)
        (cardinalBlockIso (Nat.sub_add_cancel h)) ((finAutEquiv (cardinal (q - n))).symm c)) at hac
  exact (finAutEquiv (cardinal (q - n))).symm.injective
    (blockAutHom_injective (cardinal (q - n)) (cardinal n) (cardinal q)
      (cardinalBlockIso (Nat.sub_add_cancel h)) ((finAutEquiv (cardinal q)).injective hac))

private theorem finalBlock_point {r n q : ℕ} (h : r + n = q) (x : Fin n) :
    (blockTargetSplit (cardinal r) (cardinal n) (cardinal q) (cardinalBlockIso h)).symm
      (Sum.inr (ULift.up x)) = ULift.up (Fin.cast h (x.natAdd r)) := by
  subst q
  rfl

example {r n q : ℕ} (h : r + n = q) (s : Aut (cardinal q)) :
    s ∈ (blockAutHom (cardinal r) (cardinal n) (cardinal q) (cardinalBlockIso h)).range ↔
      ∀ x : Fin n, finAutEquiv (cardinal q) s (Fin.cast h (x.natAdd r)) =
        Fin.cast h (x.natAdd r) := by
  rw [blockAutHom_range_iff]
  constructor
  · intro hfix x
    have hx := hfix (ULift.up x)
    rw [finalBlock_point h x] at hx
    have hd := congrArg ULift.down hx
    change finAutEquiv (cardinal q) s (Fin.cast h (x.natAdd r)) =
      Fin.cast h (x.natAdd r) at hd
    exact hd
  · intro hfix x
    rcases x with ⟨x⟩
    rw [finalBlock_point h x]
    apply ULift.ext
    change finAutEquiv (cardinal q) s (Fin.cast h (x.natAdd r)) = Fin.cast h (x.natAdd r)
    exact hfix x

example (a : Aut (cardinal 0)) : a = 1 := by
  apply (finAutEquiv (cardinal 0)).injective
  ext x
  exact Fin.elim0 x

example (r : ℕ) : Function.Surjective
    (blockAutHom (cardinal r) (cardinal 0) (cardinal r) (cardinalBlockIso (Nat.add_zero r))) := by
  intro s
  exact (blockAutHom_range_iff (cardinal r) (cardinal 0) (cardinal r)
    (cardinalBlockIso (Nat.add_zero r)) s).mpr (fun x => Fin.elim0 x.down)

#print axioms blockMulAction
#print axioms blockAutHom
#print axioms blockAutHom_injective
#print axioms blockAutHom_range_iff
#print axioms blockIsoEquivAut
#print axioms blockIsoEquivAut_smul
#print axioms blockIsoEquivAut_postcompose
#print axioms blockMulAction_free
#print axioms finAutEquiv

section GroupTransport
variable (R N M : SmallFinBijGroupoid) (b : R ⊗ N ≅ M)

-- The richer group equivalence retains the entire original conjugation value.
example : (splitTargetAut R N M b).toEquiv =
    (alphabetAutEquiv M).toEquiv.trans (blockTargetSplit R N M b).permCongr := rfl

example : splitTargetAut R N M b 1 = 1 := (splitTargetAut R N M b).map_one

example (a c : Aut M) :
    splitTargetAut R N M b (a * c) = splitTargetAut R N M b a * splitTargetAut R N M b c :=
  (splitTargetAut R N M b).map_mul a c

example : Aut M →* Equiv.Perm
    (ULift.{0, 0} (Fin R.of.len) ⊕ ULift.{0, 0} (Fin N.of.len)) :=
  (splitTargetAut R N M b).toMonoidHom
end GroupTransport

end FinBijBlockSubgroupTests
