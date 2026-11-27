/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Bool.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Complement of a Boolean vector.** The complement of a Boolean vector $x \in \{0,1\}^n$ is
the vector $\bar x \in \{0,1\}^n$ obtained by negating every coordinate: $\bar x_i = \lnot x_i$
for every $i < n$.

Source: JIS VOL28/Pawelski,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Pawelski/pawelski22.tex>, lines 72–81 (concept
`jis_term_d4ca78498f0fce5b71d05655`). -/
def booleanVectorComplement (n : Nat) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => !(x i)

/-- **Dual of a Boolean function.** For a Boolean function $f \colon \{0,1\}^n \to \{0,1\}$, its
dual is the Boolean function $f^\star \colon \{0,1\}^n \to \{0,1\}$ given by
$f^\star(x) = \lnot f(\bar x)$, where $\bar x$ is the coordinatewise complement of $x$. -/
def booleanFunctionDual (n : Nat) (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => !(f (booleanVectorComplement n x))

/-- **Self-dual monotone Boolean functions.** A Boolean function $f \colon \{0,1\}^n \to \{0,1\}$
is self-dual monotone when it is monotone, that is, $f(x) \le f(y)$ for all $x, y \in \{0,1\}^n$
with $x_i \le y_i$ for every $i < n$, and it equals its dual, that is, $f = f^\star$, where
$f^\star(x) = \lnot f(\bar x)$ and $\bar x$ is the coordinatewise complement of $x$. -/
def IsSelfDualMonotone (n : Nat) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x y : Fin n → Bool, (∀ i, x i ≤ y i) → f x ≤ f y) ∧ f = booleanFunctionDual n f

@[simp]
theorem booleanFunctionDual_apply (n : Nat) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    booleanFunctionDual n f x = !(f (booleanVectorComplement n x)) :=
  rfl

/-- **Complementation of Boolean vectors is an involution.** For every $n$ and every Boolean
vector $x \in \{0,1\}^n$, writing $\bar x$ for the coordinatewise complement of $x$, we have
$\bar{\bar x} = x$. -/
@[simp]
theorem booleanVectorComplement_complement (n : Nat) (x : Fin n → Bool) :
    booleanVectorComplement n (booleanVectorComplement n x) = x := by
  funext i
  simp [booleanVectorComplement]

/-- **Duality of Boolean functions is an involution.** For every $n$ and every Boolean function
$f \colon \{0,1\}^n \to \{0,1\}$, writing $f^\star$ for the dual of $f$, we have
$(f^\star)^\star = f$. -/
@[simp]
theorem booleanFunctionDual_dual (n : Nat) (f : (Fin n → Bool) → Bool) :
    booleanFunctionDual n (booleanFunctionDual n f) = f := by
  funext x
  simp [booleanFunctionDual]

/-- **Coordinate projections are self-dual monotone.** For every $n$ and every index $i < n$, the
projection $x \mapsto x_i$ on $\{0,1\}^n$ is a self-dual monotone Boolean function. -/
theorem selfDualMonotone_proj {n : Nat} (i : Fin n) :
    IsSelfDualMonotone n (fun x : Fin n → Bool => x i) := by
  refine ⟨fun x y h => h i, ?_⟩
  funext x
  simp [booleanFunctionDual, booleanVectorComplement]

end
end MetaMathlibExt
