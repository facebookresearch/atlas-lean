/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.Group.Conj

@[expose] public section

namespace MathlibExt.GroupTheory.ClassFunctionWanted

/-!
# Class functions on groups

A class function is constant on conjugacy classes. Characters of
finite-dimensional representations are the motivating examples; the space of
class functions has dimension equal to the number of conjugacy classes.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "class function over a group" (reference-only, no Lean formalization);
J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2 (functions on
a group, class functions).
-/

/-- **Class functions on a group.** Let $G$ be a group and $k$ a set. A function
$f : G \to k$ is a class function when it is constant on conjugacy classes, that is,
$f(h g h^{-1}) = f(g)$ for all $g, h \in G$. -/
def IsClassFunction {G k : Type*} [Group G] (f : G → k) : Prop :=
  ∀ g h : G, f (h * g * h⁻¹) = f g

/-- **The space of class functions.** Let $G$ be a group and $k$ a field. The space of
class functions $G \to k$ is the $k$-linear subspace of the vector space of all functions
$G \to k$, under pointwise addition and scalar multiplication, consisting of the class
functions. -/
def classFunctions (G : Type*) [Group G] (k : Type*) [Field k] :
    Submodule k (G → k) where
  carrier := {f | IsClassFunction f}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hf hg a b => by simp only [Pi.add_apply, hf a b, hg a b]
  smul_mem' := fun c f hf a b => by simp only [Pi.smul_apply, hf a b]

/--
**Characters are class functions.** Let $G$ be a group and $k$ a field. For every
finite-dimensional representation $V$ of $G$ over $k$, the character of $V$, the function
sending $g \in G$ to the trace of the linear map by which $g$ acts on $V$, is a class
function on $G$.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "class function over a group"; J.-P. Serre, Linear Representations of
Finite Groups, GTM 42, §2.1 (the character is constant on conjugacy classes).
-/
public theorem character_isClassFunction {G k : Type*} [Group G] [Field k]
    (V : FDRep k G) : IsClassFunction V.character :=
  fun g h => FDRep.char_conj V g h

private theorem classFunction_eq_of_isConj {G k : Type*} [Group G]
    {f : G → k} (hf : IsClassFunction f) {x y : G} (hxy : IsConj x y) : f x = f y := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp hxy
  exact (hf x h).symm

/-- **Class functions agree on conjugate elements.** Let $G$ be a group and let
$f : G \to k$ be a class function with values in a set $k$. If $x, y \in G$ are conjugate,
then $f(x) = f(y)$. -/
public theorem IsClassFunction.eq_of_isConj {G k : Type*} [Group G]
    {f : G → k} (hf : IsClassFunction f) {x y : G} (hxy : IsConj x y) : f x = f y :=
  classFunction_eq_of_isConj hf hxy

/--
**Class functions factor through conjugacy classes.** Let $G$ be a group and $k$ a set,
and write $[x]$ for the conjugacy class of $x \in G$. A function $f : G \to k$ is a class
function if and only if there is a function $q$ from the set of conjugacy classes of $G$
to $k$ such that $f(x) = q([x])$ for all $x \in G$.

Proof: A class function is constant on each conjugacy class, so it descends to a function
on conjugacy classes. Conversely, if $f(x) = q([x])$ for all $x \in G$, then for all
$g, h \in G$ we have $f(h g h^{-1}) = q([h g h^{-1}]) = q([g]) = f(g)$, because
$h g h^{-1}$ and $g$ are conjugate.

Proves `Wanted` entry `isClassFunction_iff_factor_conjClasses`.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "class function over a group"; J.-P. Serre, Linear Representations of
Finite Groups, GTM 42, §2 (class functions as functions on conjugacy classes).
-/
public theorem isClassFunction_iff_factor_conjClasses {G k : Type*}
    [Group G] (f : G → k) :
    IsClassFunction f ↔ ∃ g : ConjClasses G → k, ∀ x : G, f x = g (ConjClasses.mk x) := by
  constructor
  · intro hf
    exact ⟨Quotient.lift f fun _ _ => hf.eq_of_isConj, fun _ => rfl⟩
  · rintro ⟨q, hq⟩ x h
    calc
      f (h * x * h⁻¹) = q (ConjClasses.mk (h * x * h⁻¹)) := hq _
      _ = q (ConjClasses.mk x) := by
        apply congrArg q
        exact
          (ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨h, rfl⟩)).symm
      _ = f x := (hq x).symm

/-- **Class functions as functions on conjugacy classes.** Let $G$ be a group and $k$ a
field, and write $[x]$ for the conjugacy class of $x \in G$. This is the $k$-linear
isomorphism from the space of class functions $G \to k$ to the vector space of all
functions from the set of conjugacy classes of $G$ to $k$ that sends a class function $f$
to the function $[x] \mapsto f(x)$; its inverse sends a function $q$ on conjugacy classes
to the class function $x \mapsto q([x])$. -/
public def classFunctionsEquivConjClasses (G : Type*) [Group G] (k : Type*) [Field k] :
    classFunctions G k ≃ₗ[k] (ConjClasses G → k) where
  toFun f := Quotient.lift f fun _ _ => f.property.eq_of_isConj
  invFun q :=
    ⟨q ∘ ConjClasses.mk,
      (isClassFunction_iff_factor_conjClasses _).2 ⟨q, fun _ => rfl⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    rfl
  right_inv q := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl
  map_add' f g := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl
  map_smul' a f := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl

/-- **Evaluating a class function on conjugacy classes.** Let $G$ be a group and $k$ a
field. For every class function $f : G \to k$ and every $x \in G$, the function on
conjugacy classes that corresponds to $f$ under the linear isomorphism between class
functions and functions on conjugacy classes takes the value $f(x)$ at the conjugacy
class of $x$. -/
@[simp]
public theorem classFunctionsEquivConjClasses_apply_mk {G k : Type*} [Group G] [Field k]
    (f : classFunctions G k) (x : G) :
    classFunctionsEquivConjClasses G k f (ConjClasses.mk x) = (f : G → k) x :=
  rfl

/-- **Lifting a function on conjugacy classes.** Let $G$ be a group and $k$ a field. For
every function $q$ from the set of conjugacy classes of $G$ to $k$ and every $x \in G$,
the class function that corresponds to $q$ under the inverse of the linear isomorphism
between class functions and functions on conjugacy classes takes at $x$ the value of $q$
at the conjugacy class of $x$. -/
@[simp]
public theorem classFunctionsEquivConjClasses_symm_apply {G k : Type*} [Group G] [Field k]
    (q : ConjClasses G → k) (x : G) :
    (↑((classFunctionsEquivConjClasses G k).symm q) : G → k) x = q (ConjClasses.mk x) :=
  rfl

/--
**Dimension of the space of class functions.** Let $G$ be a finite group and $k$ a field.
The space of class functions $G \to k$ is a $k$-vector space whose dimension equals the
number of conjugacy classes of $G$.

Proof: The linear isomorphism between class functions and functions on conjugacy classes
reduces this to the space of all functions from the finite set of conjugacy classes of
$G$ to $k$, whose dimension is the number of conjugacy classes.

Proves `Wanted` entry `finrank_classFunctions_eq_card_conjClasses`.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "class function over a group"; J.-P. Serre, Linear Representations of
Finite Groups, GTM 42, §2.7, Theorem 6 (dimension count for class functions).
-/
public theorem finrank_classFunctions_eq_card_conjClasses (G : Type*)
    [Group G] [Fintype G] (k : Type*) [Field k] :
    Module.finrank k ↥(classFunctions G k) = Nat.card (ConjClasses G) := by
  classical
  let _ : Fintype (ConjClasses G) :=
    Fintype.ofSurjective ConjClasses.mk ConjClasses.mk_surjective
  calc
    Module.finrank k ↥(classFunctions G k) = Module.finrank k (ConjClasses G → k) :=
      (classFunctionsEquivConjClasses G k).finrank_eq
    _ = Fintype.card (ConjClasses G) := Module.finrank_fintype_fun_eq_card k
    _ = Nat.card (ConjClasses G) := Fintype.card_eq_nat_card

end MathlibExt.GroupTheory.ClassFunctionWanted
