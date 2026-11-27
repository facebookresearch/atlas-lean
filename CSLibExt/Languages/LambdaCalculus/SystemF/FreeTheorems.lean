/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.ChurchEncodings
public import CSLibExt.Languages.LambdaCalculus.SystemF.Parametricity
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence

/-!
# Free theorems for pure System F

Consequences of the fundamental theorem of relational parametricity in the
erased-term model, each a syntactic analogue of an informal free theorem.

* Naturality: for every closed typed rearrangement `r : ∀X. List X → List X` and
  every input `encList xs` built from a finite list `xs` of model terms, mapping
  before or after `r` gives beta-convertible results after the two fold arguments,
  as in Wadler's `a* ∘ r_A = r_A' ∘ a*`.
* Representation independence: counter packages whose erased operations satisfy a
  beta-invariant simulation relation are logically related at the package type,
  and every closed client of type `Package → Nat` returns, on the two packages,
  numerals that are beta-convertible once both are applied to the same two
  arguments. A unary counter and an accumulator counter with different hidden
  state types are indistinguishable by every such client, while one such client
  tells the unary counter apart from a counter whose increment does nothing.

For two packages the conclusion is relatedness at the package type, not beta
conversion, and nothing is claimed for untyped consumers. No equality of unapplied
terms, eta rule, contextual equivalence, call-by-value termination or set-valued
reading is claimed.

## References

* Philip Wadler, *Theorems for free!*, *FPCA '89*, ACM Press, 1989,
  pp. 347-359, Sections 1 and 3.1. <https://doi.org/10.1145/99370.99404>
* John C. Reynolds, *Types, Abstraction and Parametric Polymorphism*,
  *Information Processing 83*, R. E. A. Mason (ed.), North-Holland, 1983,
  pp. 513-523, Section 10.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-! ### Naturality of rearrangements -/

/-- **Right fold of model terms.** `foldModel c n xs` is `c x₀ (c x₁ (… (c xⱼ n)))`. -/
private def foldModel (c n : Model) : List Model → Model
  | [] => n
  | x :: xs => Model.app (Model.app c x) (foldModel c n xs)

/-- **Closed bodies of encoded lists are folds.** Closing the body of an open encoded list
with the fold arguments and the elements gives the right fold of the listed elements. -/
private theorem close_encListBody {k : Nat} (σ : Fin k → Model) (n c : Model)
    (is : List (Fin k)) :
    Tm.close (Fin.cases c (Fin.cases n σ)) (encListBody k is) = foldModel c n (is.map σ) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change Model.app (Model.app c (σ i)) (Tm.close _ (encListBody k is)) = _
    rw [ih]
    rfl

/-- **Erased encoded lists fold their arguments.** Applied to fold arguments `n` and `c`, the
erased encoded list of `xs` is beta-convertible to the right fold of `xs`. -/
private theorem encList_fold (xs : List Model) (n c : Model) :
    BetaEq (Model.app (Model.app (encList xs) n) c) (foldModel c n xs) := by
  have h := ((Tm.close_beta (fun i => xs.get i) (.var 0)
    (.lam (.arr (.var 1) (.arr (.var 0) (.var 0)))
      (encListBody xs.length (List.finRange xs.length))) n).appFun c).trans
    (Tm.close_beta _ _ _ c)
  rw [close_encListBody, List.map_get_finRange] at h
  exact h

/-- **The function argument of the encoded map.** The closure `λx. λr. c (f x) r` that the
encoded map passes to the list, for the environment of its four term arguments. -/
private def cmapM (f l n c : Model) : Model :=
  Tm.close (Fin.cases c (Fin.cases n (Fin.cases l (Fin.cases f Fin.elim0))))
    (.lam (.var 2) (.lam (.var 0) (.app (.app (.var 2) (.app (.var 5) (.var 1))) (.var 0))) :
      Tm 3 4)

/-- **The function argument applies `f` to each element.** -/
private theorem cmapM_red (f l n c x r : Model) :
    BetaEq (Model.app (Model.app (cmapM f l n c) x) r)
      (Model.app (Model.app c (Model.app f x)) r) :=
  ((Tm.close_beta _ _ _ x).appFun r).trans (Tm.close_beta _ _ _ r)

/-- **The erased encoded map unfolds to a fold.** -/
private theorem mapE_red (A B : Ty 0) (f l n c : Model) :
    BetaEq (Model.app (Model.app (mapE A B f l) n) c)
      (Model.app (Model.app l n) (cmapM f l n c)) := by
  refine ((((Tm.close_beta Fin.elim0 (.arr (.var 1) (.var 0)) _ f).appFun l).appFun n).appFun
    c).trans ?_
  refine (((Tm.close_beta _ (listTy (.var 1)) _ l).appFun n).appFun c).trans ?_
  refine ((Tm.close_beta _ (.var 0) _ n).appFun c).trans ?_
  exact Tm.close_beta _ (.arr (.var 1) (.arr (.var 0) (.var 0))) _ c

/-- **An encoded list is related to its image under the encoded map.** At the graph relation
of `f`, the erased encoded list of `xs` is related to the encoded map of `f` applied to it. -/
private theorem encList_graph (A B : Ty 0) (f : Model) (xs : List Model) :
    ((listTy (.var 0)).interpret (Fin.cases (Rel.graph f) Fin.elim0)).holds
      (encList xs) (mapE A B f (encList xs)) := by
  intro S n n' hn c c' hc
  refine (S.congr (encList_fold xs n c)
    ((mapE_red A B f (encList xs) n' c').trans (encList_fold xs n' _))).mpr ?_
  induction xs with
  | nil => exact hn
  | cons x xs ih =>
    exact (S.congr (BetaEq.refl _) (cmapM_red _ _ _ _ _ _)).mpr
      (hc x (Model.app f x) (BetaEq.refl _) _ _ ih)

/-- **Naturality of rearrangements.** For every closed `r : ∀X. List X → List X`,
mapping `f` after `r` agrees with `r` after mapping `f`: applied to arbitrary fold
arguments `n` and `c`, the two erased results are beta-convertible. This is the
syntactic analogue of Wadler's `a* ∘ r_A = r_A' ∘ a*`, for encoded lists of
arbitrary model terms. -/
theorem rearrangement_natural {r : Tm 0 0} (hr : Typing Fin.elim0 r rearrangeTy)
    (A B : Ty 0) (f : Model) (xs : List Model) (n c : Model) :
    BetaEq
      (Model.app (Model.app
        (mapE A B f (Model.app (Tm.eraseModel (.tapp r A)) (encList xs))) n) c)
      (Model.app (Model.app
        (Model.app (Tm.eraseModel (.tapp r B)) (mapE A B f (encList xs))) n) c) := by
  have h := fundamental_closed hr Fin.elim0 (Rel.graph f) (encList xs)
    (mapE A B f (encList xs)) (encList_graph A B f xs) Rel.betaEq n n (BetaEq.refl n)
    (cmapM f (Model.app (Tm.eraseModel r) (encList xs)) n c) c
    (fun x x' hx r r' hrr => (cmapM_red _ _ _ _ _ _).trans
      (((BetaEq.appArg c hx).appFun r).trans (BetaEq.appArg _ hrr)))
  exact (mapE_red A B f _ n c).trans h

/-- **An element-replacing list function.** The untyped term
`λl. λn. λc. l n (λx. λr. c a r)` with `a` the atom `0`, which replaces every element
of a list by `a`. -/
def constRearrange : Model :=
  ⟨.abs (.abs (.abs (.app (.app (.bvar 2) (.bvar 1))
    (.abs (.abs (.app (.app (.bvar 2) (.fvar 0)) (.bvar 0))))))), rfl⟩

/-- **Applications of atoms.** Terms built from free variables by application alone. -/
private def AtomSpine : LambdaCalculus.LocallyNameless.Untyped.Term Nat → Prop
  | .fvar _ => True
  | .app t u => AtomSpine t ∧ AtomSpine u
  | _ => False

/-- **Applications of atoms are normal.** No full-beta step starts at an application of atoms. -/
private theorem atomSpine_normal {t t' : LambdaCalculus.LocallyNameless.Untyped.Term Nat}
    (ht : AtomSpine t) : ¬ LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta t t' := by
  intro h
  induction h with
  | base hb =>
    cases hb with
    | beta => exact ht.1
  | appL _ _ ih => exact ih ht.2
  | appR _ _ ih => exact ih ht.1
  | abs => exact ht

/-- **Distinct applications of atoms are not beta-convertible.** By confluence of full-beta
reduction, two beta-convertible normal terms are equal. -/
private theorem not_betaEq_of_atomSpine {u v : Model} (hu : AtomSpine u.val)
    (hv : AtomSpine v.val) (hne : u.val ≠ v.val) : ¬ BetaEq u v := fun h =>
  hne (Relation.ChurchRosser.normal_eq (Relation.Confluent.to_churchRosser
    LambdaCalculus.LocallyNameless.Untyped.Term.confluent_fullBeta)
    (fun ⟨_, hs⟩ => atomSpine_normal hu hs) (fun ⟨_, hs⟩ => atomSpine_normal hv hs) h)

/-- **The element-replacing function as a closure.** A term with one free variable whose closure
by the atom `0` is the element-replacing function. -/
private def crTm : Tm 0 1 :=
  .lam natTy (.lam natTy (.lam natTy (.app (.app (.var 2) (.var 1))
    (.lam natTy (.lam natTy (.app (.app (.var 2) (.var 5)) (.var 0)))))))

/-- **The element-replacing function is the closure of `crTm`.** -/
private theorem constRearrange_eq : constRearrange = Tm.close (fun _ => Model.atom 0) crTm :=
  rfl

/-- **The function argument of the element-replacing function.** The closure `λx. λr. c a r`. -/
private def crK (l n c : Model) : Model :=
  Tm.close (Fin.cases c (Fin.cases n (Fin.cases l (fun _ : Fin 1 => Model.atom 0))))
    (.lam natTy (.lam natTy (.app (.app (.var 2) (.var 5)) (.var 0))) : Tm 0 4)

/-- **The element-replacing function unfolds to a fold.** -/
private theorem cr_red (l n c : Model) :
    BetaEq (Model.app (Model.app (Model.app constRearrange l) n) c)
      (Model.app (Model.app l n) (crK l n c)) := by
  rw [constRearrange_eq]
  exact (((Tm.close_beta _ natTy _ l).appFun n).appFun c).trans
    (((Tm.close_beta _ natTy _ n).appFun c).trans (Tm.close_beta _ natTy _ c))

/-- **Its function argument replaces each element by the atom `0`.** -/
private theorem crK_red (l n c x r : Model) :
    BetaEq (Model.app (Model.app (crK l n c) x) r) (Model.app (Model.app c (Model.atom 0)) r) :=
  ((Tm.close_beta _ natTy _ x).appFun r).trans (Tm.close_beta _ natTy _ r)

/-- **The element-replacing function is not natural.** For the function `atom 1`,
the one-element list `[atom 2]` and the fold arguments `atom 3` and `atom 4`, the
two sides of naturality are not beta-convertible. -/
theorem constRearrange_not_natural (A B : Ty 0) :
    ¬ BetaEq
      (Model.app (Model.app
        (mapE A B (Model.atom 1) (Model.app constRearrange (encList [Model.atom 2])))
        (Model.atom 3)) (Model.atom 4))
      (Model.app (Model.app
        (Model.app constRearrange (mapE A B (Model.atom 1) (encList [Model.atom 2])))
        (Model.atom 3)) (Model.atom 4)) := by
  intro h
  have hl := (mapE_red A B (Model.atom 1) _ (Model.atom 3) (Model.atom 4)).trans
    ((cr_red _ (Model.atom 3) _).trans ((encList_fold [Model.atom 2] (Model.atom 3) _).trans
      ((crK_red _ _ _ (Model.atom 2) (Model.atom 3)).trans
        (cmapM_red _ _ _ _ (Model.atom 0) (Model.atom 3)))))
  have hr := (cr_red _ (Model.atom 3) (Model.atom 4)).trans
    ((mapE_red A B (Model.atom 1) _ (Model.atom 3) _).trans
      ((encList_fold [Model.atom 2] (Model.atom 3) _).trans
        ((cmapM_red _ _ _ _ (Model.atom 2) (Model.atom 3)).trans
          (crK_red _ _ _ _ (Model.atom 3)))))
  exact not_betaEq_of_atomSpine (by simp [AtomSpine, Model.app, Model.atom])
    (by simp [AtomSpine, Model.app, Model.atom]) (by decide) (hl.symm.trans (h.trans hr))

/-! ### Representation independence -/

/-- **Lifted implementations erase to the originals.** Weakening a closed implementation into
the body of `pack` does not change its erasure. -/
private theorem close_pack_impl (σ : Fin 1 → Model) (t : Tm 0 0) :
    Tm.close σ ((t.tyRename Fin.succ).rename Fin.elim0) = Tm.eraseModel t := by
  apply Subtype.ext
  change Tm.eraseWith _ (Tm.rename Fin.elim0 (Tm.tyRename Fin.succ t)) = Tm.eraseWith _ t
  rw [Tm.eraseWith_rename, Tm.tyRename, Tm.eraseWith_tySubst]
  congr 1
  funext i
  exact Fin.elim0 i

/-- **A packed counter passes its implementation to the consumer.** -/
private theorem pack_red (T : Ty 0) (new inc get : Tm 0 0) (k : Model) :
    BetaEq (Model.app (Tm.eraseModel (pack T new inc get)) k)
      (Model.app (Model.app (Model.app k (Tm.eraseModel new)) (Tm.eraseModel inc))
        (Tm.eraseModel get)) := by
  have h := Tm.close_beta Fin.elim0 counterConsumerTy
    (.app (.app (.app (.tapp (.var 0) (T.rename Fin.succ))
      ((new.tyRename Fin.succ).rename Fin.elim0))
      ((inc.tyRename Fin.succ).rename Fin.elim0))
      ((get.tyRename Fin.succ).rename Fin.elim0)) k
  simp only [Tm.close_app, Tm.close_tapp, Tm.close_var] at h
  rw [close_pack_impl, close_pack_impl, close_pack_impl] at h
  exact h

/-- **Related counter packages.** If a beta-invariant relation `R` relates the two
initial states, is preserved by the two increments, and sends related states to
observations related as numerals, then the two packed counters are related at the
package type. -/
theorem packages_related {T₁ T₂ : Ty 0} {new₁ inc₁ get₁ new₂ inc₂ get₂ : Tm 0 0}
    (R : Rel) (hnew : R.holds (Tm.eraseModel new₁) (Tm.eraseModel new₂))
    (hinc : ∀ x y, R.holds x y →
      R.holds (Model.app (Tm.eraseModel inc₁) x) (Model.app (Tm.eraseModel inc₂) y))
    (hget : ∀ x y, R.holds x y →
      ((natTy : Ty 0).interpret Fin.elim0).holds
        (Model.app (Tm.eraseModel get₁) x) (Model.app (Tm.eraseModel get₂) y)) :
    (packageTy.interpret Fin.elim0).holds
      (Tm.eraseModel (pack T₁ new₁ inc₁ get₁)) (Tm.eraseModel (pack T₂ new₂ inc₂ get₂)) := by
  intro Q k k' hk
  refine (Q.congr (pack_red T₁ new₁ inc₁ get₁ k) (pack_red T₂ new₂ inc₂ get₂ k')).mpr ?_
  exact hk R _ _ hnew _ _ hinc _ _ hget

/-- **Representation independence.** Under the hypotheses of `packages_related`,
every closed client `e : Package → Nat` gives beta-convertible observations on the two
packed counters, applied to arbitrary arguments `s` and `z`. -/
theorem package_clients_agree {T₁ T₂ : Ty 0} {new₁ inc₁ get₁ new₂ inc₂ get₂ : Tm 0 0}
    (R : Rel) (hnew : R.holds (Tm.eraseModel new₁) (Tm.eraseModel new₂))
    (hinc : ∀ x y, R.holds x y →
      R.holds (Model.app (Tm.eraseModel inc₁) x) (Model.app (Tm.eraseModel inc₂) y))
    (hget : ∀ x y, R.holds x y →
      ((natTy : Ty 0).interpret Fin.elim0).holds
        (Model.app (Tm.eraseModel get₁) x) (Model.app (Tm.eraseModel get₂) y))
    {e : Tm 0 0} (he : Typing Fin.elim0 e (.arr packageTy natTy)) (s z : Model) :
    BetaEq
      (Model.app (Model.app
        (Model.app (Tm.eraseModel e) (Tm.eraseModel (pack T₁ new₁ inc₁ get₁))) s) z)
      (Model.app (Model.app
        (Model.app (Tm.eraseModel e) (Tm.eraseModel (pack T₂ new₂ inc₂ get₂))) s) z) := by
  exact fundamental_closed he Fin.elim0 _ _
    (packages_related (T₁ := T₁) (T₂ := T₂) R hnew hinc hget) Rel.betaEq s s
    (fun _ _ h => BetaEq.appArg s h) z z (BetaEq.refl z)

/-! ### Two counters -/

/-- **Unary counter.** The state is a numeral, the initial state is zero, the
increment is the successor and the observation is the identity. -/
def unaryPackage : Tm 0 0 := pack natTy zeroTm succTm (idTm natTy)

/-- **Accumulator state type.** The type `Nat → Nat`. -/
def accTy {n : Nat} : Ty n := .arr natTy natTy

/-- **Accumulator initial state.** The identity on numerals. -/
def accNew : Tm 0 0 := idTm natTy

/-- **Accumulator increment.** The term `λh. λm. succ (h m)`. -/
def accInc : Tm 0 0 := .lam accTy (.lam natTy (.app succTm (.app (.var 1) (.var 0))))

/-- **Accumulator observation.** The term `λh. h zero`. -/
def accGet : Tm 0 0 := .lam accTy (.app (.var 0) zeroTm)

/-- **Accumulator counter.** After `k` increments the state is a function sending each
numeral `m` to `m + k`, and the observation applies it to zero. -/
def accumulatorPackage : Tm 0 0 := pack accTy accNew accInc accGet

/-- **The unary counter is well typed.** -/
theorem unaryPackage_typed : Typing Fin.elim0 unaryPackage packageTy := by
  exact pack_typed (zeroTm_typed _) (succTm_typed _) (idTm_typed _ _)

/-- **The accumulator increment is well typed.** -/
theorem accInc_typed : Typing Fin.elim0 accInc (.arr accTy accTy) := by
  exact .lam (.lam (.app (succTm_typed _) (.app (.var 1) (.var 0))))

/-- **The accumulator observation is well typed.** -/
theorem accGet_typed : Typing Fin.elim0 accGet (.arr accTy natTy) := by
  exact .lam (.app (.var 0) (zeroTm_typed _))

/-- **The accumulator counter is well typed.** -/
theorem accumulatorPackage_typed : Typing Fin.elim0 accumulatorPackage packageTy := by
  exact pack_typed (idTm_typed _ _) accInc_typed accGet_typed

/-- **Counter simulation relation.** Relates a unary state `x` to an accumulator state
`h` when there is a count `k` such that, for all model terms `m`, `s` and `z`, the term
`x s z` is beta-convertible to `s` applied `k` times to `z`, and `h m s z` is
beta-convertible to `s` applied `k` times to `m s z`. -/
def counterRel : Rel where
  holds x h := ∃ k : Nat,
    (∀ s z, BetaEq (Model.app (Model.app x s) z) ((Model.app s)^[k] z)) ∧
      ∀ m s z, BetaEq (Model.app (Model.app (Model.app h m) s) z)
        ((Model.app s)^[k] (Model.app (Model.app m s) z))
  congr := by
    intro f f' g g' hf hg
    constructor
    · rintro ⟨k, h1, h2⟩
      exact ⟨k, fun s z => ((hf.appFun s).appFun z).symm.trans (h1 s z),
        fun m s z => (((hg.appFun m).appFun s).appFun z).symm.trans (h2 m s z)⟩
    · rintro ⟨k, h1, h2⟩
      exact ⟨k, fun s z => ((hf.appFun s).appFun z).trans (h1 s z),
        fun m s z => (((hg.appFun m).appFun s).appFun z).trans (h2 m s z)⟩

/-- **Zero applied to two arguments returns the second.** -/
private theorem zero_red (s z : Model) :
    BetaEq (Model.app (Model.app (Tm.eraseModel (zeroTm : Tm 0 0)) s) z) z :=
  ((Tm.close_beta (n := 1) Fin.elim0 (.arr (.var 0) (.var 0)) (.lam (.var 0) (.var 0))
    s).appFun z).trans (Tm.close_beta _ _ _ z)

/-- **The identity returns its argument.** -/
private theorem id_red (A : Ty 0) (x : Model) :
    BetaEq (Model.app (Tm.eraseModel (idTm A : Tm 0 0)) x) x :=
  Tm.close_beta _ _ _ x

/-- **The successor adds one application.** -/
private theorem succ_red (x s z : Model) :
    BetaEq (Model.app (Model.app (Model.app (Tm.eraseModel (succTm : Tm 0 0)) x) s) z)
      (Model.app s (Model.app (Model.app x s) z)) :=
  (((Tm.close_beta Fin.elim0 natTy _ x).appFun s).appFun z).trans
    (((Tm.close_beta (n := 1) _ (.arr (.var 0) (.var 0)) _ s).appFun z).trans
      (Tm.close_beta _ _ _ z))

/-- **Iterated application respects beta conversion of the start.** -/
private theorem iter_congr (s : Model) {a b : Model} (h : BetaEq a b) (k : Nat) :
    BetaEq ((Model.app s)^[k] a) ((Model.app s)^[k] b) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact BetaEq.appArg s ih

/-- **Iterated application preserves a relation.** -/
private theorem iter_rel (S : Rel) {s s' : Model}
    (hs : ∀ a b, S.holds a b → S.holds (Model.app s a) (Model.app s' b)) {z z' : Model}
    (hz : S.holds z z') (k : Nat) :
    S.holds ((Model.app s)^[k] z) ((Model.app s')^[k] z') := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hs _ _ ih

/-- **The initial states are related.** The counter simulation relation relates zero
to the identity on numerals. -/
theorem counterRel_new :
    counterRel.holds (Tm.eraseModel (zeroTm : Tm 0 0)) (Tm.eraseModel accNew) := by
  exact ⟨0, fun s z => zero_red s z, fun m s z => ((id_red natTy m).appFun s).appFun z⟩

/-- **The increments preserve the relation.** If the counter simulation relation relates
`x` and `h`, it relates the successor of `x` to the incremented accumulator state. -/
theorem counterRel_inc {x h : Model} (hxh : counterRel.holds x h) :
    counterRel.holds (Model.app (Tm.eraseModel (succTm : Tm 0 0)) x)
      (Model.app (Tm.eraseModel accInc) h) := by
  obtain ⟨k, h1, h2⟩ := hxh
  refine ⟨k + 1, fun s z => ?_, fun m s z => ?_⟩
  · rw [Function.iterate_succ_apply']
    exact (succ_red x s z).trans (BetaEq.appArg s (h1 s z))
  have hacc : BetaEq
      (Model.app (Model.app (Model.app (Model.app (Tm.eraseModel accInc) h) m) s) z)
      (Model.app (Model.app (Model.app (Tm.eraseModel (succTm : Tm 0 0)) (Model.app h m)) s)
        z) :=
    ((((Tm.close_beta Fin.elim0 accTy _ h).appFun m).appFun s).appFun z).trans
      (((Tm.close_beta _ natTy _ m).appFun s).appFun z)
  rw [Function.iterate_succ_apply']
  exact hacc.trans ((succ_red _ s z).trans (BetaEq.appArg s (h2 m s z)))

/-- **Related states give numeral-related observations.** If the counter simulation
relation relates `x` and `h`, the two observations are related at the numeral type. -/
theorem counterRel_get {x h : Model} (hxh : counterRel.holds x h) :
    ((natTy : Ty 0).interpret Fin.elim0).holds
      (Model.app (Tm.eraseModel (idTm natTy : Tm 0 0)) x) (Model.app (Tm.eraseModel accGet) h) := by
  obtain ⟨k, h1, h2⟩ := hxh
  intro S s s' hs z z' hz
  refine (S.congr ((((id_red natTy x).appFun s).appFun z).trans (h1 s z)) ?_).mpr
    (iter_rel S hs hz k)
  exact (((Tm.close_beta Fin.elim0 accTy _ h).appFun s').appFun z').trans
    ((h2 _ s' z').trans (iter_congr s' (zero_red s' z') k))

/-- **Typed clients do not distinguish the unary and accumulator counters.** Every closed client
`e : Package → Nat` gives beta-convertible observations on the unary counter and the
accumulator counter, applied to arbitrary arguments `s` and `z`. -/
theorem counters_indistinguishable {e : Tm 0 0}
    (he : Typing Fin.elim0 e (.arr packageTy natTy)) (s z : Model) :
    BetaEq
      (Model.app (Model.app (Model.app (Tm.eraseModel e) (Tm.eraseModel unaryPackage)) s) z)
      (Model.app (Model.app
        (Model.app (Tm.eraseModel e) (Tm.eraseModel accumulatorPackage)) s) z) := by
  exact package_clients_agree (T₁ := natTy) (T₂ := accTy) counterRel counterRel_new
    (fun _ _ h => counterRel_inc h) (fun _ _ h => counterRel_get h) he s z

/-! ### Non-vacuity -/

/-- **Stuck counter.** The unary counter with the identity as increment. -/
def stuckPackage : Tm 0 0 := pack natTy zeroTm (idTm natTy) (idTm natTy)

/-- **The stuck counter is well typed.** -/
theorem stuckPackage_typed : Typing Fin.elim0 stuckPackage packageTy := by
  exact pack_typed (zeroTm_typed _) (idTm_typed _ _) (idTm_typed _ _)

/-- **Distinguishing client.** The client `λp. p [Nat] (ΛX. λnew. λinc. λget. get (inc new))`,
which observes the state after one increment. -/
def distinguishingClient : Tm 0 0 :=
  .lam packageTy (.app (.tapp (.var 0) natTy)
    (.tabs (.lam (.var 0) (.lam (.arr (.var 0) (.var 0)) (.lam (.arr (.var 0) natTy)
      (.app (.var 0) (.app (.var 1) (.var 2))))))))

/-- **The distinguishing client is well typed.** -/
theorem distinguishingClient_typed :
    Typing Fin.elim0 distinguishingClient (.arr packageTy natTy) := by
  have h := Typing.tapp (A := natTy) (Typing.var (Γ := Fin.cases packageTy Fin.elim0) 0)
  exact .lam (.app h (.tabs (.lam (.lam (.lam (.app (.var 0) (.app (.var 1) (.var 2))))))))

/-- **The distinguishing client observes one increment.** On a packed counter the client is
beta-convertible to the observation of the incremented initial state. -/
private theorem client_red (T : Ty 0) (new inc get : Tm 0 0) :
    BetaEq (Model.app (Tm.eraseModel distinguishingClient) (Tm.eraseModel (pack T new inc get)))
      (Model.app (Tm.eraseModel get) (Model.app (Tm.eraseModel inc) (Tm.eraseModel new))) := by
  have h := Tm.close_beta Fin.elim0 packageTy
    (.app (.tapp (.var 0) natTy) (.tabs (.lam (.var 0) (.lam (.arr (.var 0) (.var 0))
      (.lam (.arr (.var 0) natTy) (.app (.var 0) (.app (.var 1) (.var 2))))))))
    (Tm.eraseModel (pack T new inc get))
  simp only [Tm.close_app, Tm.close_tapp, Tm.close_var, Tm.close_tabs, Fin.cases_zero] at h
  refine h.trans ((pack_red T new inc get _).trans ?_)
  exact (((Tm.close_beta _ _ _ _).appFun _).appFun _).trans
    (((Tm.close_beta _ _ _ _).appFun _).trans (Tm.close_beta _ _ _ _))

/-- **The client tells the unary and stuck counters apart.** On the arguments `atom 0`
and `atom 1` the two observations are not beta-convertible. -/
theorem stuck_counter_distinguished :
    ¬ BetaEq
      (Model.app (Model.app (Model.app (Tm.eraseModel distinguishingClient)
        (Tm.eraseModel unaryPackage)) (Model.atom 0)) (Model.atom 1))
      (Model.app (Model.app (Model.app (Tm.eraseModel distinguishingClient)
        (Tm.eraseModel stuckPackage)) (Model.atom 0)) (Model.atom 1)) := by
  intro h
  have hu := ((((client_red natTy zeroTm succTm (idTm natTy)).appFun (Model.atom 0)).appFun
    (Model.atom 1)).trans ((((id_red natTy _).appFun (Model.atom 0)).appFun (Model.atom 1)).trans
      ((succ_red _ (Model.atom 0) (Model.atom 1)).trans
        (BetaEq.appArg (Model.atom 0) (zero_red (Model.atom 0) (Model.atom 1))))))
  have hs := ((((client_red natTy zeroTm (idTm natTy) (idTm natTy)).appFun (Model.atom 0)).appFun
    (Model.atom 1)).trans ((((id_red natTy _).appFun (Model.atom 0)).appFun (Model.atom 1)).trans
      ((((id_red natTy _).appFun (Model.atom 0)).appFun (Model.atom 1)).trans
        (zero_red (Model.atom 0) (Model.atom 1)))))
  exact not_betaEq_of_atomSpine (by simp [AtomSpine, Model.app, Model.atom])
    (by simp [AtomSpine, Model.atom]) (by decide) (hu.symm.trans (h.trans hs))

/-- **No simulation relates the unary and stuck counters.** No beta-invariant relation
satisfies the hypotheses of `packages_related` for the unary counter and the stuck
counter. -/
theorem not_exists_simulation_unary_stuck :
    ¬ ∃ R : Rel, R.holds (Tm.eraseModel (zeroTm : Tm 0 0)) (Tm.eraseModel (zeroTm : Tm 0 0)) ∧
      (∀ x y, R.holds x y →
        R.holds (Model.app (Tm.eraseModel (succTm : Tm 0 0)) x)
          (Model.app (Tm.eraseModel (idTm natTy : Tm 0 0)) y)) ∧
      ∀ x y, R.holds x y →
        ((natTy : Ty 0).interpret Fin.elim0).holds
          (Model.app (Tm.eraseModel (idTm natTy : Tm 0 0)) x)
          (Model.app (Tm.eraseModel (idTm natTy : Tm 0 0)) y) := by
  rintro ⟨R, hnew, hinc, hget⟩
  exact stuck_counter_distinguished (package_clients_agree (T₁ := natTy) (T₂ := natTy) R hnew
    hinc hget distinguishingClient_typed (Model.atom 0) (Model.atom 1))

end Cslib.Languages.LambdaCalculus.SystemF
