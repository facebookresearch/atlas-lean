/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.TracesOfIrreducibleQuadratics

/-!
# Tests for the set $U_q$ of traces of irreducible quadratics
-/

set_option autoImplicit false

@[expose] public section

open Polynomial FiniteField

open scoped Pointwise

namespace TracesOfIrreducibleQuadraticsTest

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- $x^2 + 1$ is irreducible over $\mathbb{F}_3$, so $0 \in U_3$. -/
example : (0 : ZMod 3) ∈ tracesOfIrreducibleQuadratics (ZMod 3) :=
  mem_tracesOfIrreducibleQuadratics_iff.2 (by decide)

/-- $x^2 - 2x + 1 = (x - 1)^2$, so $2 \notin U_5$. -/
example : (2 : ZMod 5) ∉ tracesOfIrreducibleQuadratics (ZMod 5) := by
  rw [mem_tracesOfIrreducibleQuadratics_iff]
  decide

/-- $3 \in U_7$ and $-3 = 4 \in U_7$. -/
example : (3 : ZMod 7) ∈ tracesOfIrreducibleQuadratics (ZMod 7) ∧
    (4 : ZMod 7) ∈ tracesOfIrreducibleQuadratics (ZMod 7) := by
  have h3 : (3 : ZMod 7) ∈ tracesOfIrreducibleQuadratics (ZMod 7) :=
    mem_tracesOfIrreducibleQuadratics_iff.2 (by decide)
  refine ⟨h3, ?_⟩
  rw [show (4 : ZMod 7) = -3 by decide]
  exact neg_mem_tracesOfIrreducibleQuadratics_iff.2 h3

/-- $U_q$ is nonempty and $0 \in U_q + U_q$ for $q = 2$. -/
example : (tracesOfIrreducibleQuadratics (ZMod 2)).Nonempty ∧
    (0 : ZMod 2) ∈
      tracesOfIrreducibleQuadratics (ZMod 2) + tracesOfIrreducibleQuadratics (ZMod 2) :=
  ⟨nonempty_tracesOfIrreducibleQuadratics, zero_mem_tracesOfIrreducibleQuadratics_add_self⟩

/-- $U_3$ is the set of traces of the elements of $\mathbb{F}_9 \setminus \mathbb{F}_3$ of norm
$1$. -/
example : tracesOfIrreducibleQuadratics (ZMod 3) =
    Algebra.trace (ZMod 3) (GaloisField 3 2) ''
      {β | β ∉ Set.range (algebraMap (ZMod 3) (GaloisField 3 2)) ∧
        Algebra.norm (ZMod 3) β = 1} :=
  tracesOfIrreducibleQuadratics_eq_image_trace (GaloisField.finrank 3 (by norm_num))

/-- So $0 \in U_3$ is the trace of some $\beta \in \mathbb{F}_9 \setminus \mathbb{F}_3$ of norm
$1$. -/
example : ∃ β : GaloisField 3 2, β ∉ Set.range (algebraMap (ZMod 3) (GaloisField 3 2)) ∧
    Algebra.norm (ZMod 3) β = 1 ∧ Algebra.trace (ZMod 3) (GaloisField 3 2) β = 0 := by
  have h0 : (0 : ZMod 3) ∈ tracesOfIrreducibleQuadratics (ZMod 3) :=
    mem_tracesOfIrreducibleQuadratics_iff.2 (by decide)
  rw [tracesOfIrreducibleQuadratics_eq_image_trace (L := GaloisField 3 2)
    (GaloisField.finrank 3 (by norm_num))] at h0
  obtain ⟨β, ⟨hβ, hN⟩, hT⟩ := h0
  exact ⟨β, hβ, hN, hT⟩

#check @FiniteField.tracesOfIrreducibleQuadratics
#check @FiniteField.mem_tracesOfIrreducibleQuadratics_iff
#check @FiniteField.neg_mem_tracesOfIrreducibleQuadratics_iff
#check @FiniteField.map_mem_tracesOfIrreducibleQuadratics_iff
#check @FiniteField.nonempty_tracesOfIrreducibleQuadratics
#check @FiniteField.zero_mem_tracesOfIrreducibleQuadratics_add_self
#check @FiniteField.tracesOfIrreducibleQuadratics_eq_image_trace

end TracesOfIrreducibleQuadraticsTest
