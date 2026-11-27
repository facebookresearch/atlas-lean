/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Erasure
public import CSLibExt.Languages.LambdaCalculus.SystemF.Relations
public import CSLibExt.Languages.LambdaCalculus.SystemF.Typing

/-!
# Church encodings in pure System F

Church-encoded lists with their map, Church numerals, and the Leivant encoding
of an existential counter interface, built from type variables, arrows and
universal types only. Each of these encodings is a pure System F term with a
typing theorem; no constructor is added to the syntax and no fixpoint is used.
The open list term `encListTm k` has type `List X` in a context of `k` element
variables of type `X`. Its closure `encList xs : Model` substitutes arbitrary model
terms for those variables, so the elements of `encList xs` need not be erasures of
typed terms. The closed lists `encList xs`, the beta-conversion relation and the
graph relation of a model term are the inputs the free theorems instantiate.

## Main definitions

* `listTy`, `mapTm`, `encListTm`: the list type, the encoded map as a fold, and
  the typed open list term.
* `encList`: the open list term closed by a list of model terms.
* `natTy`, `zeroTm`, `succTm`: Church numerals.
* `packageTy`, `pack`: counter packages `∃X. X × (X → X) × (X → Nat)` in the
  Leivant encoding.
* `Rel.betaEq`, `Rel.graph`: beta-invariant relations.

## References

* Philip Wadler, *Theorems for free!*, *FPCA '89*, ACM Press, 1989,
  pp. 347-359, Section 4. <https://doi.org/10.1145/99370.99404>
* John C. Reynolds, *Types, Abstraction and Parametric Polymorphism*,
  *Information Processing 83*, R. E. A. Mason (ed.), North-Holland, 1983,
  pp. 513-523, Section 10.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-! ### Lists -/

/-- **Church-encoded lists.** The type `∀R. R → (A → R → R) → R` of lists with
elements of type `A`. -/
def listTy {n : Nat} (A : Ty n) : Ty n :=
  .all (.arr (.var 0) (.arr (.arr (A.rename Fin.succ) (.arr (.var 0) (.var 0))) (.var 0)))

/-- **Rearrangements.** The type `∀X. List X → List X` of list functions that
cannot inspect the elements. -/
def rearrangeTy : Ty 0 := .all (.arr (listTy (.var 0)) (listTy (.var 0)))

/-- **Type of the encoded map.** The type `∀X. ∀Y. (X → Y) → List X → List Y`. -/
def mapTy : Ty 0 :=
  .all (.all (.arr (.arr (.var 1) (.var 0)) (.arr (listTy (.var 1)) (listTy (.var 0)))))

/-- **Encoded map.** The term `ΛX. ΛY. λf. λl. ΛR. λn. λc. l [R] n (λx. λr. c (f x) r)`,
a fold over the encoded list. -/
def mapTm : Tm 0 0 :=
  .tabs (.tabs (.lam (.arr (.var 1) (.var 0)) (.lam (listTy (.var 1))
    (.tabs (.lam (.var 0) (.lam (.arr (.var 1) (.arr (.var 0) (.var 0)))
      (.app (.app (.tapp (.var 2) (.var 0)) (.var 1))
        (.lam (.var 2) (.lam (.var 0)
          (.app (.app (.var 2) (.app (.var 5) (.var 1))) (.var 0)))))))))))

/-- **Type application at a computed type.** A type application has the type `T` whenever the
instantiated body of the universal type is `T`. -/
private theorem typing_tapp_of_eq {n m : Nat} {Γ : Ctx n m} {f : Tm n m} {A : Ty n}
    {C : Ty (n + 1)} {T : Ty n} (hf : Typing Γ f (.all C)) (h : C.instantiate A = T) :
    Typing Γ (.tapp f A) T := h ▸ .tapp hf

/-- **The encoded map is well typed.** The encoded map has the type
`∀X. ∀Y. (X → Y) → List X → List Y`. -/
theorem mapTm_typed : Typing Fin.elim0 mapTm mapTy := by
  exact .tabs (.tabs (.lam (.lam (.tabs (.lam (.lam
    (.app (.app (typing_tapp_of_eq (.var 2) rfl) (.var 1)) (.lam (.lam
      (.app (.app (.var 2) (.app (.var 5) (.var 1))) (.var 0)))))))))))

/-- **Body of an open encoded list.** The term `c x₀ (c x₁ (… (c xⱼ n)))` for the
listed element variables, where `c` and `n` are the two newest term variables and
the element variables lie above them. -/
def encListBody (k : Nat) : List (Fin k) → Tm 2 (k + 2)
  | [] => .var 1
  | i :: is => .app (.app (.var 0) (.var (i.addNat 2))) (encListBody k is)

/-- **Open encoded list.** The term `ΛR. λn. λc. c x₀ (c x₁ (… (c xₖ₋₁ n)))` over
`k` element variables `x₀, …, xₖ₋₁`. -/
def encListTm (k : Nat) : Tm 1 k :=
  .tabs (.lam (.var 0) (.lam (.arr (.var 1) (.arr (.var 0) (.var 0)))
    (encListBody k (List.finRange k))))

/-- **Bodies of open encoded lists are well typed.** In the context of the two fold arguments
and the element variables, the body over any list of element variables has the result type. -/
private theorem encListBody_typed (k : Nat) (is : List (Fin k)) :
    Typing (Fin.cases (.arr (.var 1) (.arr (.var 0) (.var 0)))
      (Fin.cases (.var 0) (fun _ : Fin k => ((.var 0 : Ty 1).rename Fin.succ))))
      (encListBody k is) (.var 0) := by
  induction is with
  | nil => exact .var 1
  | cons i is ih => exact .app (.app (.var 0) (.var (i.addNat 2))) ih

/-- **Open encoded lists are well typed.** When the `k` element variables have the
element type, the open encoded list has the list type. -/
theorem encListTm_typed (k : Nat) :
    Typing (fun _ : Fin k => (.var 0 : Ty 1)) (encListTm k) (listTy (.var 0)) := by
  exact .tabs (.lam (.lam (encListBody_typed k (List.finRange k))))

/-- **Erased encoded list.** The encoded list whose elements are the given model
terms, obtained by closing the open encoded list. -/
def encList (xs : List Model) : Model :=
  Tm.close (fun i => xs.get i) (encListTm xs.length)

/-- **Erased encoded map.** The erasure of the encoded map at element types `A` and
`B`, applied to a function `f` and a list `l`. -/
def mapE (A B : Ty 0) (f l : Model) : Model :=
  Model.app (Model.app (Tm.eraseModel (.tapp (.tapp mapTm A) B)) f) l

/-! ### Numerals -/

/-- **Church numerals.** The type `∀X. (X → X) → X → X`, at every type depth. -/
def natTy {n : Nat} : Ty n := .all (.arr (.arr (.var 0) (.var 0)) (.arr (.var 0) (.var 0)))

/-- **Zero.** The numeral `ΛX. λs. λz. z`. -/
def zeroTm {n m : Nat} : Tm n m :=
  .tabs (.lam (.arr (.var 0) (.var 0)) (.lam (.var 0) (.var 0)))

/-- **Successor.** The term `λk. ΛX. λs. λz. s (k [X] s z)`. -/
def succTm {n m : Nat} : Tm n m :=
  .lam natTy (.tabs (.lam (.arr (.var 0) (.var 0)) (.lam (.var 0)
    (.app (.var 1) (.app (.app (.tapp (.var 2) (.var 0)) (.var 1)) (.var 0))))))

/-- **Identity at a type.** The term `λx : A. x`. -/
def idTm {n m : Nat} (A : Ty n) : Tm n m := .lam A (.var 0)

/-- **Zero is a numeral.** Zero has the numeral type in every context. -/
theorem zeroTm_typed {n m : Nat} (Γ : Ctx n m) : Typing Γ zeroTm natTy := by
  exact .tabs (.lam (.lam (.var 0)))

/-- **The successor maps numerals to numerals.** In every context the successor has
the type `Nat → Nat`. -/
theorem succTm_typed {n m : Nat} (Γ : Ctx n m) : Typing Γ succTm (.arr natTy natTy) := by
  exact .lam (.tabs (.lam (.lam (.app (.var 1)
    (.app (.app (typing_tapp_of_eq (.var 2) rfl) (.var 1)) (.var 0))))))

/-- **The identity is well typed.** In every context the identity at `A` has the type
`A → A`. -/
theorem idTm_typed {n m : Nat} (Γ : Ctx n m) (A : Ty n) : Typing Γ (idTm A) (.arr A A) := by
  exact .lam (.var 0)

/-! ### Counter packages -/

/-- **Counter consumers.** The type `∀X. X → (X → X) → (X → Nat) → Y` of consumers of
a counter with hidden state type `X`, where the result type `Y` is the outer type
variable. -/
def counterConsumerTy : Ty 1 :=
  .all (.arr (.var 0) (.arr (.arr (.var 0) (.var 0)) (.arr (.arr (.var 0) natTy) (.var 1))))

/-- **Counter packages.** The type `∀Y. (∀X. X → (X → X) → (X → Nat) → Y) → Y`, the
Leivant encoding of the existential type `∃X. X × (X → X) × (X → Nat)`. -/
def packageTy : Ty 0 := .all (.arr counterConsumerTy (.var 0))

/-- **Packing a counter.** The term `ΛY. λk. k [T] new inc get`, which hides the state
type `T` of the implementation `new`, `inc`, `get`. -/
def pack (T : Ty 0) (new inc get : Tm 0 0) : Tm 0 0 :=
  .tabs (.lam counterConsumerTy
    (.app (.app (.app (.tapp (.var 0) (T.rename Fin.succ))
      ((new.tyRename Fin.succ).rename Fin.elim0))
      ((inc.tyRename Fin.succ).rename Fin.elim0))
      ((get.tyRename Fin.succ).rename Fin.elim0)))

/-- **Packed counters are well typed.** An implementation with initial state of type
`T`, increment of type `T → T` and observation of type `T → Nat` packs to a term of
the package type. -/
theorem pack_typed {T : Ty 0} {new inc get : Tm 0 0}
    (hn : Typing Fin.elim0 new T) (hi : Typing Fin.elim0 inc (.arr T T))
    (hg : Typing Fin.elim0 get (.arr T natTy)) :
    Typing Fin.elim0 (pack T new inc get) packageTy := by
  refine .tabs (.lam (.app (.app (.app (typing_tapp_of_eq (.var 0) rfl) ?_) ?_) ?_))
  · exact (hn.tyRename Fin.succ).rename Fin.elim0 (fun i => Fin.elim0 i)
  · exact (hi.tyRename Fin.succ).rename Fin.elim0 (fun i => Fin.elim0 i)
  · exact (hg.tyRename Fin.succ).rename Fin.elim0 (fun i => Fin.elim0 i)

/-! ### Relations -/

namespace Rel

/-- **Beta-conversion relation.** Relates two model terms exactly when they are
beta-convertible. -/
def betaEq : Rel where
  holds := BetaEq
  congr := by
    intro f f' g g' hf hg
    exact ⟨fun h => hf.symm.trans (h.trans hg), fun h => hf.trans (h.trans hg.symm)⟩

/-- **Graph relation.** Relates `a` to `b` exactly when `f a` is beta-convertible to
`b`. -/
def graph (f : Model) : Rel where
  holds a b := BetaEq (Model.app f a) b
  congr := by
    intro a a' b b' ha hb
    exact ⟨fun h => (BetaEq.appArg f ha).symm.trans (h.trans hb),
      fun h => (BetaEq.appArg f ha).trans (h.trans hb.symm)⟩

end Rel

end Cslib.Languages.LambdaCalculus.SystemF
