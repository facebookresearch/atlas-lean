/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.ModelTheory.Semantics

/-!
# The first-order language of groups

The first-order language with one constant (the identity), one unary
function (inversion), and one binary function (multiplication),
together with its canonical structure on any group. Extracted from
the `ProPFiniteAxiomatizability` statement (Kourovka 21.120), where
it was source-local, once a second conjecture needed the same
language.
-/

@[expose] public section

namespace FirstOrder.Language

universe u

/-- **Group function symbols.** The function symbols of the first-order language of groups,
graded by arity, are a constant symbol for the identity (arity $0$), a symbol for inversion
(arity $1$) and a symbol for multiplication (arity $2$); there are no others. -/
inductive GroupFunction : ℕ → Type
  | one : GroupFunction 0
  | inv : GroupFunction 1
  | mul : GroupFunction 2

/-- **The first-order language of groups.** The first-order language of groups has the group
function symbols (a constant for the identity, a unary symbol for inversion and a binary symbol
for multiplication) as its function symbols and no relation symbols. -/
def groupLanguage : FirstOrder.Language where
  Functions := GroupFunction
  Relations := fun _ => Empty

/-- **The canonical structure on a group.** For a group $G$, the canonical structure on $G$ for
the first-order language of groups interprets the identity constant as the identity $1$ of $G$,
inversion as $x \mapsto x^{-1}$ and multiplication as $(x, y) \mapsto xy$; there are no
relation symbols to interpret. -/
@[reducible]
def groupLanguageStructure (G : Type u) [Group G] : groupLanguage.Structure G where
  funMap := fun {_} f x =>
    match f with
    | .one => 1
    | .inv => (x 0)⁻¹
    | .mul => x 0 * x 1
  RelMap := fun {_} r => nomatch r

/-- **The function symbols of the language of groups.** For every $n \in \mathbb{N}$, the
$n$-ary function symbols of the first-order language of groups are exactly the group function
symbols of arity $n$. -/
theorem groupLanguage_functions (n : ℕ) :
    groupLanguage.Functions n = GroupFunction n := rfl

/-- **The language of groups has no relation symbols.** For every $n \in \mathbb{N}$, the
first-order language of groups has no $n$-ary relation symbols. -/
theorem groupLanguage_relations (n : ℕ) :
    groupLanguage.Relations n = Empty := rfl

/-- **Multiplication in the canonical structure.** For every group $G$ and every pair
$(x_0, x_1)$ of elements of $G$, the multiplication symbol of the language of groups,
interpreted in the canonical structure on $G$, sends $(x_0, x_1)$ to $x_0 x_1$. -/
theorem groupLanguageStructure_mul (G : Type u) [Group G] (x : Fin 2 → G) :
    (groupLanguageStructure G).funMap GroupFunction.mul x = x 0 * x 1 := rfl

/-- **Inversion in the canonical structure.** For every group $G$ and every one-element tuple
$(x_0)$ of elements of $G$, the inversion symbol of the language of groups, interpreted in the
canonical structure on $G$, sends $(x_0)$ to $x_0^{-1}$. -/
theorem groupLanguageStructure_inv (G : Type u) [Group G] (x : Fin 1 → G) :
    (groupLanguageStructure G).funMap GroupFunction.inv x = (x 0)⁻¹ := rfl

/-- **The identity in the canonical structure.** For every group $G$, the identity constant
symbol of the language of groups, interpreted in the canonical structure on $G$, takes the value
$1$ at the empty tuple, where $1$ is the identity of $G$. -/
theorem groupLanguageStructure_one (G : Type u) [Group G] (x : Fin 0 → G) :
    (groupLanguageStructure G).funMap GroupFunction.one x = 1 := rfl

end FirstOrder.Language
