/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Representation_exists_ne_zero_forall_apply_eq_of_isPGroup.lean`
and
`P2M/Sol/S_Representation_exists_ne_zero_forall_apply_eq_of_isPGroup.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Basic

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public section

namespace Representation

/-- A nonzero representation of a finite `p`-group over a field of
characteristic `p` has a nonzero fixed vector.

The `ℤ/p`-span of one nonzero orbit is a finite `p`-group module, so the
fixed-point counting congruence for `p`-group actions gives a fixed point
other than zero. -/
public theorem exists_ne_zero_forall_apply_eq_of_isPGroup
    {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {v : V} (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ g : G, ρ g w = w := by
  classical
  letI modp : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
  have hsmul : ∀ (c : ZMod p) (x : V),
      c • x = ((ZMod.castHom (dvd_refl p) k c : k)) • x := fun _ _ => rfl
  set S : Set V := Set.range fun g : G => ρ g v with hS
  set W : Submodule (ZMod p) V := Submodule.span (ZMod p) S with hW
  have hWstab : ∀ (g : G) {x : V}, x ∈ W → ρ g x ∈ W := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    | zero => rw [map_zero]; exact W.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact W.add_mem hy hz
    | smul c y _ hy => rw [hsmul, map_smul, ← hsmul]; exact W.smul_mem c hy
  haveI : Module.Finite (ZMod p) W :=
    Module.Finite.span_of_finite (ZMod p) (Set.finite_range _)
  haveI : Finite W := Module.finite_of_finite (ZMod p)
  letI act : MulAction G W :=
    { smul := fun g w => ⟨ρ g w, hWstab g w.2⟩
      one_smul := fun w => Subtype.ext (by show ρ 1 (w : V) = w; rw [map_one]; rfl)
      mul_smul := fun g h w => Subtype.ext (by
        show ρ (g * h) (w : V) = ρ g (ρ h w); rw [map_mul]; rfl) }
  have hact : ∀ (g : G) (w : W), ((g • w : W) : V) = ρ g w := fun _ _ => rfl
  have hmod := hG.card_modEq_card_fixedPoints W
  have hvW : (⟨v, Submodule.subset_span ⟨1, by simp⟩⟩ : W) ≠ 0 :=
    fun h => hv (congrArg Subtype.val h)
  have hpW : p ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := W), Nat.card_zmod]
    refine dvd_pow_self p
      (Module.finrank_pos_iff.mpr ⟨⟨_, 0, hvW⟩⟩).ne'
  have hpF : p ∣ Nat.card (MulAction.fixedPoints G W) := by
    apply Nat.dvd_of_mod_eq_zero
    have h1 : Nat.card W % p = 0 := Nat.mod_eq_zero_of_dvd hpW
    have h2 : Nat.card W % p = Nat.card (MulAction.fixedPoints G W) % p := hmod
    omega
  have h0 : (0 : W) ∈ MulAction.fixedPoints G W :=
    fun g => Subtype.ext (by rw [hact]; exact map_zero _)
  haveI : Finite (MulAction.fixedPoints G W) := inferInstance
  have hcard : 1 < Nat.card (MulAction.fixedPoints G W) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints G W) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
    exact lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hpF)
  rw [Finite.one_lt_card_iff_nontrivial] at hcard
  obtain ⟨⟨y, hy⟩, hy0⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints G W)
  refine ⟨(y : V), fun h => hy0 (Subtype.ext (Subtype.ext h)), fun g => ?_⟩
  have hgy := hy g
  rw [Subtype.ext_iff, hact] at hgy
  exact hgy

end Representation
