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

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Defs

@[expose] public section

namespace Set

variable {M : Type*} [Mul M]

/-- **Product-free set.** A set $S$ in a type $M$ with a multiplication is product-free if
$xy \notin S$ for all $x, y \in S$, where $x$ and $y$ need not be distinct. -/
def IsProductFree (S : Set M) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x * y ∉ S

end Set
