/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CoveringSystem

/-!
# Translating a covering system

`MetaMathlibExt.isCoveringSystem_translate` proves that adding a fixed integer to every
residue of a covering system preserves coverage of the integers.
-/

namespace MetaMathlibExt

/-- **Translating a covering system.** Let $C$ be a covering system: a finite set of
congruences $x \equiv a_i \pmod{m_i}$ with $a_i \in \mathbb{Z}$ and $m_i \in \mathbb{N}$ (where
$x \equiv a_i \pmod 0$ means $x = a_i$) such that every integer satisfies at least one of them.
Then for every $t \in \mathbb{Z}$ the congruences $x \equiv a_i + t \pmod{m_i}$ also form a
covering system.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 3 (`integers-2026-A38-lem-3`). -/
public theorem isCoveringSystem_translate (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (t : ℤ) :
    Int.IsCoveringSystem (classes.image fun c => (c.1 + t, c.2)) := by
  intro z
  obtain ⟨c, hc, hzc⟩ := hcov (z - t)
  refine ⟨_, Finset.mem_image_of_mem _ hc, ?_⟩
  simpa only [sub_add_cancel] using hzc.add_right t

end MetaMathlibExt
