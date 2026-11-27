/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open Pointwise

/--
**Covering system.** A covering system of a commutative semiring $R$ is a finite family of cosets
$r_i + I_i = \{r_i + a : a \in I_i\}$, where each $I_i$ is an ideal of $R$ different from both
$\{0\}$ and $R$, whose union is all of $R$. In the case $R = \mathbb{Z}$, this corresponds to a
choice of finitely many congruences $x \equiv r_i \pmod{n_i}$ with moduli $n_i \ge 2$ such that
every integer satisfies at least one of them.
-/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = @Set.univ R
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

/--
**Strict covering system.** A covering system of a commutative semiring $R$, given by cosets
$r_i + I_i$, is strict if the ideals $I_i$ are pairwise distinct. In the case $R = \mathbb{Z}$, this
means that the congruences defining it have pairwise distinct moduli.

This corresponds to the notion of covering system that Erdős and Graham use.

Source: [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
theory. Monographies de L'Enseignement Mathematique (1980).
-/
structure StrictCoveringSystem (R : Type*) [CommSemiring R] extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace CoveringSystem

variable {R : Type*} [CommSemiring R]

def coset (c : CoveringSystem R) (i : c.ι) : Set R :=
  {c.residue i} + c.moduli i

@[simp]
theorem iUnion_cosets (c : CoveringSystem R) : ⋃ i, c.coset i = Set.univ :=
  c.unionCovers

end CoveringSystem

namespace Int

public def IsCoveringSystem (classes : Finset (ℤ × ℕ)) : Prop :=
  ∀ z : ℤ, ∃ c ∈ classes, Int.ModEq (c.2 : ℤ) z c.1

public def indexedCoveringClasses {k : ℕ} (moduli : Fin k → ℕ)
    (residues : Fin k → ℤ) : Finset (ℤ × ℕ) :=
  Finset.univ.image fun i => (residues i, moduli i)

public theorem indexedCoveringClasses_isCoveringSystem_iff {k : ℕ}
    (moduli : Fin k → ℕ) (residues : Fin k → ℤ) :
    Int.IsCoveringSystem (Int.indexedCoveringClasses moduli residues) ↔
      ∀ z : ℤ, ∃ i, z ≡ residues i [ZMOD (moduli i : ℤ)] := by
  unfold IsCoveringSystem indexedCoveringClasses
  constructor
  · intro h z
    obtain ⟨c, hc, hcov⟩ := h z
    rw [Finset.mem_image] at hc
    obtain ⟨i, _, rfl⟩ := hc
    exact ⟨i, hcov⟩
  · intro h z
    obtain ⟨i, hi⟩ := h z
    exact ⟨(residues i, moduli i),
      Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩

end Int
