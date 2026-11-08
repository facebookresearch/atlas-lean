/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner, Nam Trang
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 6, Logic 7, Logic 22, Logic 38

/-!
# `MathlibExt.SetTheory.Tree.Basic`

## References

* Jech (for `IsTree`, `level`, `IsNormalTreeAt`)
* Kunen (for `IsTreeAt`)
-/

namespace MetaMathlibExt

-- Logic 6: Tree

/-- A *tree* is a partially ordered set (T, <) iwith the property that for each x ∈ T, the set {  y
∈ T : y < x  } of all predecessors of x is well-ordered by <).
-/
def IsTree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  ∀ x : α, IsChain (· ≤ ·) {y : α | y < x}

-- Logic 7: Level of a well-founded partial ordering

/-- For an ordinal α, the *α-th level* of a well-founded partial order (T, <) is Lev_α(T) = {  x ∈ T
: ht(x) = α  }, the set of elements whose height equals α.
-/
def level.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] (a : Ordinal.{u}) : Set α :=
  {x : α | WellFounded.rank (· < ·) x = a}

-- Logic 22: $\kappa$ tree

open Cardinal in

 /-- A κ-tree is a tree on κ whose levels are of cardinality < κ. -/
 def IsTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsTree α ∧
    (∀ x : α, ∃ a < κ.ord, x ∈ level α a) ∧
    (∀ a < κ.ord, (level α a).Nonempty ∧ #(level α a) < κ)

-- Logic 38: Normal tree

/-- Let κ be a cardinal and (α,≤) a well-founded partial order; for x∈α let rank(x) denote the rank
of x in the well-founded relation <. α is a *normal tree at κ* if:

\begin{enumerate}
  \item $\alpha$ is a tree at $\kappa$, i.e.
  \begin{itemize}
    \item $\forall x\in\alpha$, $\{y \mid y<x\}$ is a chain,
    \item $\forall x\in\alpha,\ \exists a<\kappa.\mathrm{ord},\ x\in\mathrm{level}_\alpha(a)$,
    \item $\forall a<\kappa.\mathrm{ord},\ \mathrm{level}_\alpha(a)\neq\emptyset$
          and $|\mathrm{level}_\alpha(a)|<\kappa$;
  \end{itemize}
  \item $\alpha$ has a root: $\exists r\in\alpha\ \forall x\in\alpha,\ r\le x$;
  \item every node can be extended to any higher level below $\kappa$:
  \[
    \forall x\in\alpha\ \forall b<\kappa.\mathrm{ord}\;
    \bigl(\operatorname{rank}(x)<b \to
    \exists y\in\alpha\ (x<y \land \operatorname{rank}(y)=b)\bigr);
  \]
  \item every node splits:
  \[
    \forall x\in\alpha\ \exists y,z\in\alpha\;
    \bigl(x<y \land x<z \land y\not\le z \land z\not\le y\bigr).
  \]
\end{enumerate}
-/
def IsNormalTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  IsTreeAt κ α ∧
  (∃ r : α, ∀ x : α, r ≤ x) ∧
  (∀ x : α, ∀ b : Ordinal.{u},
      WellFounded.rank (· < ·) x < b → b < κ.ord →
      ∃ y : α, x < y ∧ WellFounded.rank (· < ·) y = b) ∧
  (∀ x : α, ∃ y z : α, x < y ∧ x < z ∧ ¬ (y ≤ z) ∧ ¬ (z ≤ y))

end MetaMathlibExt

end
