/-
Copyright 2026 The Formal Conjectures Authors.

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


public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.SetTheory.Ordinal.Exponential

@[expose] public section

/-!
# Ordinal Ramsey property

Ported from `FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean`
in google-deepmind/formal-conjectures.
-/

open Cardinal Ordinal

universe u

/--
**Ordinal–cardinal Ramsey property.** For ordinals $\alpha$, $\beta$ and a cardinal $c$, the
partition property $\alpha \to (\beta, c)^2$ holds if for every coloring of the edges of the
complete graph on the ordinals less than $\alpha$ in red and blue, either some set of vertices
whose order type is $\beta$ has all its edges red, or some set of vertices of cardinality exactly
$c$ has all its edges blue.
-/
def OrdinalCardinalRamsey (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  -- For any 2-coloring of `α`,
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    -- either there is a red `K_β`
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
   -- or there is a blue `K_c`.
    ∃ s, blue.IsClique s ∧ #s = c
