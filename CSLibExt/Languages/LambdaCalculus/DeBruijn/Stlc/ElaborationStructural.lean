/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Structural laws for certified STLC elaboration
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Elaboration

/-!
# Structural laws for raw STLC terms

This module relates structural operations on the extrinsic surface language to
the corresponding intrinsically typed operations.  The main result states
that erasure commutes with any type-preserving variable renaming whose action
on de Bruijn indices is known.  Weakening is obtained as a direct corollary.

Separating these laws from the elaborator keeps the executable checker small
while giving downstream developments a reusable interface for moving checked
programs between contexts.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Ξ : List (Ty Base)}

namespace RawTm

/-- **Lifting a numerical renaming.** Given a renaming $\rho : \mathbb{N} \to \mathbb{N}$ of
de Bruijn indices, its lift through one binder is the map $\mathbb{N} \to \mathbb{N}$ sending
$0$ to $0$ and $n + 1$ to $\rho(n) + 1$. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- **Renaming of raw terms.** Given a map $\rho : \mathbb{N} \to \mathbb{N}$ on de Bruijn indices,
renaming a raw term by $\rho$ replaces each variable $n$ by $\rho(n)$, renames both parts of an
application by $\rho$, and renames the body of a lambda abstraction, keeping its parameter type,
by the lifted map $\rho'$ given by $\rho'(0) = 0$ and $\rho'(n + 1) = \rho(n) + 1$. -/
def rename (ρ : Nat → Nat) : RawTm Base → RawTm Base
  | .var n => .var (ρ n)
  | .app f a => RawTm.app (rename ρ f) (rename ρ a)
  | .lam A body => RawTm.lam A (rename (liftRen ρ) body)

@[simp] theorem liftRen_zero (ρ : Nat → Nat) : liftRen ρ 0 = 0 := rfl

@[simp] theorem liftRen_succ (ρ : Nat → Nat) (n : Nat) :
    liftRen ρ (n + 1) = ρ n + 1 := rfl

@[simp] theorem liftRen_id : liftRen id = id := by
  funext n
  cases n <;> rfl

/-- **Lifting commutes with composition of numerical renamings.** For maps
$\rho, \sigma : \mathbb{N} \to \mathbb{N}$, the lift of $\sigma \circ \rho$ through one binder
equals the lift of $\sigma$ composed after the lift of $\rho$. -/
theorem liftRen_comp (ρ σ : Nat → Nat) :
    liftRen (σ ∘ ρ) = liftRen σ ∘ liftRen ρ := by
  funext n
  cases n <;> rfl

@[simp] theorem rename_var (ρ : Nat → Nat) (n : Nat) :
    rename ρ (RawTm.var n : RawTm Base) = RawTm.var (ρ n) := rfl

@[simp] theorem rename_app (ρ : Nat → Nat) (f a : RawTm Base) :
    rename ρ (RawTm.app f a) = RawTm.app (rename ρ f) (rename ρ a) := rfl

@[simp] theorem rename_lam (ρ : Nat → Nat) (A : Ty Base) (body : RawTm Base) :
    rename ρ (RawTm.lam A body) = RawTm.lam A (rename (liftRen ρ) body) := rfl

@[simp] theorem rename_id (t : RawTm Base) : rename id t = t := by
  induction t with
  | var n => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A body ih => simp [ih]

/-- **Composition of renamings of raw terms.** For all maps
$\rho, \sigma : \mathbb{N} \to \mathbb{N}$ and every raw term $t$, renaming $t$ by $\rho$ and then
renaming the result by $\sigma$ gives the same raw term as renaming $t$ by the composite
$\sigma \circ \rho$. -/
theorem rename_comp (ρ σ : Nat → Nat) (t : RawTm Base) :
    rename σ (rename ρ t) = rename (σ ∘ ρ) t := by
  induction t generalizing ρ σ with
  | var n => rfl
  | app f a ihf iha => simp [ihf, iha]
  | lam A body ih =>
      simp only [rename_lam]
      rw [ih, liftRen_comp]

/-- **Renaming preserves the size of a raw term.** For every map $\rho : \mathbb{N} \to \mathbb{N}$
and every raw term $t$, the renaming of $t$ by $\rho$ has the same number of syntax nodes as $t$. -/
@[simp] theorem size_rename (ρ : Nat → Nat) (t : RawTm Base) :
    (rename ρ t).size = t.size := by
  induction t generalizing ρ with
  | var n => rfl
  | app f a ihf iha => simp [RawTm.size, ihf, iha]
  | lam A body ih => simp [RawTm.size, ih]

/-- **Shifting preserves the size of a raw term.** For all natural numbers $k$ and $c$ and every
raw term $t$, shifting $t$ by $k$ at cutoff $c$ (adding $k$ to each variable index that is at
least the cutoff, which grows by one under each binder) gives a raw term with the same number
of syntax nodes as $t$. -/
@[simp] theorem size_shift (amount cutoff : Nat) (t : RawTm Base) :
    (t.shift amount cutoff).size = t.size := by
  induction t generalizing cutoff with
  | var n => simp [RawTm.shift, RawTm.size]
  | app f a ihf iha => simp [RawTm.shift, RawTm.size, ihf, iha]
  | lam A body ih => simp [RawTm.shift, RawTm.size, ih]

/-- **Indices occurring in a raw term.** The list of de Bruijn indices of a raw term, read
from left to right with repetitions: a variable with index $n$ gives $[n]$, an application
gives the indices of the function followed by those of the argument, and a lambda abstraction
gives the indices of its body, unshifted.

Bound occurrences are intentionally included, so this list is useful for diagnostics rather
than for scoping. -/
def indices : RawTm Base → List Nat
  | .var n => [n]
  | .app f a => indices f ++ indices a
  | .lam _ body => indices body

@[simp] theorem indices_var (n : Nat) :
    indices (RawTm.var n : RawTm Base) = [n] := rfl

@[simp] theorem indices_app (f a : RawTm Base) :
    indices (RawTm.app f a) = indices f ++ indices a := rfl

@[simp] theorem indices_lam (A : Ty Base) (body : RawTm Base) :
    indices (RawTm.lam A body) = indices body := rfl

/-- **Free indices of a raw term.** For a binder depth $d$ and a raw term $t$, the free
indices of $t$ at depth $d$ form a list defined by recursion on $t$: a variable with index $n$
contributes $[n - d]$ if $d \le n$ and the empty list otherwise; an application contributes
the free indices of the function followed by those of the argument, both at depth $d$; and a
lambda abstraction contributes the free indices of its body at depth $d + 1$. -/
def freeIndices : Nat → RawTm Base → List Nat
  | depth, .var n => if depth ≤ n then [n - depth] else []
  | depth, .app f a => freeIndices depth f ++ freeIndices depth a
  | depth, .lam _ body => freeIndices (depth + 1) body

/-- **Closed raw terms.** A raw term $t$ is closed when its list of free indices at binder
depth $0$ is empty. -/
def Closed (t : RawTm Base) : Prop := freeIndices 0 t = []

instance (t : RawTm Base) : Decidable t.Closed := by
  unfold Closed
  infer_instance

@[simp] theorem freeIndices_var_zero (n : Nat) :
    freeIndices 0 (RawTm.var n : RawTm Base) = [n] := by
  simp [freeIndices]

@[simp] theorem freeIndices_app (depth : Nat) (f a : RawTm Base) :
    freeIndices depth (RawTm.app f a) =
      freeIndices depth f ++ freeIndices depth a := rfl

@[simp] theorem freeIndices_lam (depth : Nat) (A : Ty Base) (body : RawTm Base) :
    freeIndices depth (RawTm.lam A body) = freeIndices (depth + 1) body := rfl

@[simp] theorem closed_app (f a : RawTm Base) :
    Closed (RawTm.app f a) ↔ Closed f ∧ Closed a := by
  simp [Closed, freeIndices]

end RawTm

/-- **Agreement of a typed and a numerical renaming.** A typed renaming $\rho$ from context
$\Gamma$ to context $\Delta$ agrees with a map $r : \mathbb{N} \to \mathbb{N}$ when, for every
type $A$ and every variable $x$ of type $A$ in $\Gamma$, the de Bruijn index of $\rho(x)$
equals $r$ applied to the de Bruijn index of $x$. -/
def RenAgrees (ρ : Ren Γ Δ) (r : Nat → Nat) : Prop :=
  ∀ {A} (x : Var Γ A), (ρ x).toNat = r x.toNat

@[simp] theorem renAgrees_id : RenAgrees (Var.id : Ren Γ Γ) id := by
  intro A x
  rfl

/-- **Agreement of renamings is preserved by lifting.** Let $\rho$ be a typed renaming from
context $\Gamma$ to $\Delta$ and let $r : \mathbb{N} \to \mathbb{N}$ be a numerical renaming
that agrees with $\rho$. Then for every type $A$, the lift of $\rho$ under a binder of type
$A$ agrees with the lift of $r$ through one binder. -/
theorem RenAgrees.lift {ρ : Ren Γ Δ} {r : Nat → Nat} (h : RenAgrees ρ r) :
    RenAgrees (Var.lift (A := A) ρ) (RawTm.liftRen r) := by
  intro B x
  cases x with
  | zero => rfl
  | succ x => simp [RawTm.liftRen, Var.toNat, h x]

/-- **Agreement of renamings is preserved by composition.** Let $\rho$ be a typed renaming
from context $\Gamma$ to $\Delta$, let $\sigma$ be a typed renaming from $\Delta$ to $\Xi$,
and let $r, s : \mathbb{N} \to \mathbb{N}$. If $\rho$ agrees with $r$ and $\sigma$ agrees with
$s$, then the composite renaming that applies $\rho$ and then $\sigma$ agrees with
$s \circ r$. -/
theorem RenAgrees.comp {ρ : Ren Γ Δ} {r : Nat → Nat}
    {σ : Ren Δ Ξ} {s : Nat → Nat}
    (hρ : RenAgrees ρ r) (hσ : RenAgrees σ s) :
    RenAgrees (Var.comp ρ σ) (s ∘ r) := by
  intro A x
  exact (hσ (ρ x)).trans (congrArg s (hρ x))

/-- **Erasure commutes with renaming.** Let $\rho$ be a typed renaming from context $\Gamma$
to $\Delta$ and let $r : \mathbb{N} \to \mathbb{N}$ be a numerical renaming that agrees with
$\rho$. Then for every intrinsically typed term $t$ of type $A$ in context $\Gamma$, the
erasure of the renamed term $\rho(t)$ equals the raw renaming by $r$ (lifted at every binder)
of the erasure of $t$. -/
theorem Tm.erase_rename (ρ : Ren Γ Δ) (r : Nat → Nat)
    (h : RenAgrees ρ r) (t : Tm Γ A) :
    (Tm.rename ρ t).erase = RawTm.rename r t.erase := by
  induction t generalizing Δ r with
  | var x => simp [Tm.erase, h x]
  | app f a ihf iha => simp [Tm.erase, ihf ρ r h, iha ρ r h]
  | @lam A B Γ body ih =>
      simp [Tm.erase, ih (Var.lift ρ) (RawTm.liftRen r) h.lift]

/-- **Erasure of a weakened term.** For every intrinsically typed term $t$ in context $\Gamma$
and every type $B$, the erasure of the weakening of $t$ to the context $\Gamma$ extended by
$B$ equals the raw renaming by the successor map $n \mapsto n + 1$ (lifted at every binder)
of the erasure of $t$. Thus every free index is incremented by one. -/
@[simp] theorem Tm.erase_weaken (t : Tm Γ A) :
    (Tm.weaken (B := B) t).erase = RawTm.rename Nat.succ t.erase := by
  apply Tm.erase_rename
  intro C x
  rfl

/-- **Agreeing numerical renamings coincide on erased terms.** Let $\rho$ be a type-preserving
renaming of variables from context $\Gamma$ to context $\Delta$, and let
$r, s : \mathbb{N} \to \mathbb{N}$ both agree with $\rho$: for every variable $x$ of $\Gamma$, the
de Bruijn index of $\rho(x)$ is the image of the index of $x$ under $r$, and also under $s$. Then
for every intrinsically typed term $t$ of type $A$ in context $\Gamma$, renaming the erasure of $t$
by $r$ and renaming it by $s$ give the same raw term. -/
theorem RawTm.rename_eq_on_erase (ρ : Ren Γ Δ) (r s : Nat → Nat)
    (hr : RenAgrees ρ r) (hs : RenAgrees ρ s) (t : Tm Γ A) :
    RawTm.rename r t.erase = RawTm.rename s t.erase := by
  rw [← Tm.erase_rename ρ r hr, ← Tm.erase_rename ρ s hs]

end Cslib.Languages.LambdaCalculus.Stlc
