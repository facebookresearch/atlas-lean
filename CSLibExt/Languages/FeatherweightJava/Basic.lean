/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Relation

/-!
Finite Featherweight Java core after Cornell CS 4110 Lecture #30
(Igarashi, Pierce, Wadler): classes, inheritance, constructors by
parameter list, fields, methods, casts; excludes interfaces,
assignment, overloading, exceptions, generics; no soundness claim.
-/

@[expose] public section
set_option autoImplicit false
namespace Cslib.FeatherweightJava

/-- Class names, as natural numbers (Lecture #30 classes). -/
abbrev CName := Nat

/-- Method names, as natural numbers (Lecture #30 methods). -/
abbrev MName := Nat

/-- Field names, as natural numbers (Lecture #30 fields). -/
abbrev FName := Nat

/-- Variable names, as natural numbers (Lecture #30 variables). -/
abbrev VName := Nat

/-- Root class Object, the name `0`; well-formed tables do not declare it (Lecture #30). -/
def Object : CName := 0

/-- The this variable, the variable name `0` (Lecture #30). -/
def thisVar : VName := 0

mutual
  /-- Featherweight Java expressions (Lecture #30 syntax). -/
  inductive Expr where
  | var (x : VName)
  | fld (recv : Expr) (field : FName)
  | invk (recv : Expr) (method : MName) (args : Expr.Args)
  | new (cls : CName) (args : Expr.Args)
  | cast (cls : CName) (expr : Expr)
  deriving DecidableEq

  /-- Argument lists for invocations and new (Lecture #30 syntax). -/
  inductive Expr.Args where
  | nil
  | cons (head : Expr) (tail : Expr.Args)
  deriving DecidableEq
end

/-- Convert Args to List Expr (helper). -/
def Expr.Args.toList : Expr.Args -> List Expr
  | .nil => []
  | .cons head tail => head :: tail.toList

/-- Length of Args (helper for arity check). -/
def Expr.Args.length : Expr.Args -> Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

mutual
  /-- Class names referenced by an expression, as a list with repeats kept: receiver first, then
  arguments; `new` and casts prepend their class (helper for WellFormed). -/
  def Expr.classRefs : Expr → List CName :=
    fun e => match e with
    | .var _ => []
    | .fld recv _ => Expr.classRefs recv
    | .invk recv _ args => Expr.classRefs recv ++ Expr.Args.classRefs args
    | .new cls args => cls :: Expr.Args.classRefs args
    | .cast cls expr => cls :: Expr.classRefs expr

  /-- Class names referenced by an argument list, concatenated left to right with repeats kept
  (helper for WellFormed). -/
  def Expr.Args.classRefs : Expr.Args → List CName :=
    fun args => match args with
    | .nil => []
    | .cons head tail => Expr.classRefs head ++ Expr.Args.classRefs tail
end

/-- Method declaration: return, params, body (Lecture #30). -/
structure MethodDecl where
  ret : CName
  params : List (CName × VName)
  body : Expr
deriving DecidableEq

/-- Class declaration: name, superclass, typed fields, constructor parameters and named methods;
no constructor body is stored (Lecture #30 classes). -/
structure ClassDecl where
  name : CName
  super : CName
  fields : List (CName × FName)
  ctorParams : List (CName × FName)
  methods : List (MName × MethodDecl)
deriving DecidableEq

/-- Class names a class declaration references, as a list with repeats kept: superclass, field
classes, constructor parameter classes, then each method's return, parameter and body classes
(helper for WellFormed). -/
def ClassDecl.classRefs (cd : ClassDecl) : List CName :=
  cd.super :: (cd.fields.map Prod.fst ++ cd.ctorParams.map Prod.fst ++
    cd.methods.flatMap fun p =>
      p.2.ret :: (p.2.params.map Prod.fst ++ Expr.classRefs p.2.body))

/-- Class table as a list of declarations (Lecture #30). -/
abbrev ClassTable := List ClassDecl

/-- Find class by name in table (helper). -/
def lookupClass (ct : ClassTable) (C : CName) : Option ClassDecl :=
  ct.find? (fun cd => cd.name == C)

/-- Direct subclass edge (Lecture #30 S-CLASS base). -/
def directExtends (ct : ClassTable) (C D : CName) : Prop :=
  ∃ cd ∈ ct, cd.name = C ∧ cd.super = D

/-- Subtyping via reflexive-transitive closure (S-REFL/S-TRANS/S-CLASS). -/
def Subtype (ct : ClassTable) : CName → CName → Prop :=
  Relation.ReflTransGen (directExtends ct)

/-- Fuel-bounded superclass chain worker (helper for F/MB/MT). -/
def supersAux (ct : ClassTable) : Nat → CName → List CName :=
  fun fuel C => match fuel, C with
  | 0, _ => []
  | fuel + 1, C =>
    if C = Object then [Object]
    else match lookupClass ct C with
    | none => [C]
    | some cd => C :: supersAux ct fuel cd.super

/-- Superclass chain from `C`, at most `ct.length + 1` names: it stops at Object, at an
undeclared class, or at the fuel bound (helper). -/
def supers (ct : ClassTable) (C : CName) : List CName :=
  supersAux ct (ct.length + 1) C

/-- Field lookup with superclass fields first (F-OBJECT/F-CLASS). -/
def fields (ct : ClassTable) (C : CName) : Option (List (CName × FName)) :=
  if C = Object then some []
  else
    let step (acc : Option (List (CName × FName))) (D : CName) :
        Option (List (CName × FName)) :=
      match acc with
      | none => none
      | some fs =>
        if D = Object then some fs
        else match lookupClass ct D with
        | none => none
        | some cd => some (cd.fields ++ fs)
    (supers ct C).foldl step (some [])

/-- The first method declaration named `m` found walking the superclass chain of `C` upward,
skipping `Object` and undeclared classes; it returns the declaration, not the class declaring it
(MB-CLASS/MB-SUPER). -/
def lookupMethod (ct : ClassTable) (m : MName) (C : CName) :
    Option MethodDecl :=
  (supers ct C).findSome? fun D =>
    if D = Object then none
    else
      (lookupClass ct D).bind fun cd =>
        (cd.methods.find? fun p => p.1 == m).map Prod.snd

/-- Method type lookup: the parameter classes and return class of the method found by
`lookupMethod`, or `none` (MT-CLASS/MT-SUPER). -/
def mtype (ct : ClassTable) (m : MName) (C : CName) :
    Option (List CName × CName) :=
  (lookupMethod ct m C).map fun md => (md.params.map Prod.fst, md.ret)

/-- Method body lookup: the parameter names and body of the method found by `lookupMethod`, or
`none` (MB-CLASS/MB-SUPER). -/
def mbody (ct : ClassTable) (m : MName) (C : CName) :
    Option (List VName × Expr) :=
  (lookupMethod ct m C).map fun md => (md.params.map Prod.snd, md.body)

/-- Override check: parent sig must match (OVERRIDE). -/
def override (ct : ClassTable) (m : MName) (D : CName)
    (sig : List CName × CName) : Prop :=
  ∀ sig', mtype ct m D = some sig' → sig' = sig

/-- Well-formedness of a class table: no declared class is named `Object`; class names are
distinct; every class a declaration refers to is `Object` or declared; the superclass chain of
each declared class repeats no class; method names are distinct within each class; the field
names that `fields` returns are distinct; each method has the signature of the method of the
same name found from its superclass, if there is one; and method parameters are distinct and
differ from `this`. -/
structure WellFormed (ct : ClassTable) : Prop where
  objectUndeclared : ∀ cd ∈ ct, cd.name ≠ Object
  namesNodup : (ct.map ClassDecl.name).Nodup
  refsDeclared : ∀ cd ∈ ct, ∀ C ∈ cd.classRefs, C = Object ∨ ∃ d ∈ ct,
    d.name = C
  supersNodup : ∀ cd ∈ ct, (supers ct cd.name).Nodup
  methodNamesNodup : ∀ cd ∈ ct, (cd.methods.map Prod.fst).Nodup
  fieldNamesNodup : ∀ (C : CName) (fs : List (CName × FName)),
    fields ct C = some fs → (fs.map Prod.snd).Nodup
  overrideOk : ∀ cd ∈ ct, ∀ p ∈ cd.methods,
    override ct p.1 cd.super (p.2.params.map Prod.fst, p.2.ret)
  methodParamsOk : ∀ cd ∈ ct, ∀ p ∈ cd.methods,
    (p.2.params.map Prod.snd).Nodup ∧ thisVar ∉ p.2.params.map Prod.snd

mutual
  /-- Values are fully evaluated new-expressions (Lecture #30 values). -/
  inductive Value : Expr → Prop where
  | new (C : CName) (args : Expr.Args) : ArgsValue args → Value (.new C args)

  /-- All-valuable argument lists (Lecture #30 values). -/
  inductive ArgsValue : Expr.Args → Prop where
  | nil : ArgsValue .nil
  | cons {head : Expr} {tail : Expr.Args} :
    Value head → ArgsValue tail → ArgsValue (.cons head tail)
end

mutual
  /-- Substitute variables in expression (helper for E-INVK). -/
  def substMany (s : List (VName × Expr)) : Expr → Expr :=
    fun e => match e with
    | .var x =>
      match s.find? (fun p => p.1 == x) with
      | some (_, e) => e
      | none => .var x
    | .fld recv field => .fld (substMany s recv) field
    | .invk recv method args =>
      .invk (substMany s recv) method (substArgs s args)
    | .new cls args => .new cls (substArgs s args)
    | .cast cls expr => .cast cls (substMany s expr)

  /-- Substitute variables in argument lists (helper for E-INVK). -/
  def substArgs (s : List (VName × Expr)) : Expr.Args → Expr.Args :=
    fun args => match args with
    | .nil => .nil
    | .cons head tail => .cons (substMany s head) (substArgs s tail)
end

/-- Positional field value lookup (helper for E-PROJ). -/
def fieldValue : List (CName × FName) → Expr.Args → FName → Option Expr :=
  fun fs args g => match fs, args with
  | [], _ => none
  | _, .nil => none
  | (_, f) :: tl, .cons v vs =>
    if f == g then some v else fieldValue tl vs g

/-- Pair parameter names with argument expressions position by position, truncating to the
shorter list; E-INVK checks that the arguments are values and that the lengths agree (helper for
E-INVK). -/
def zipArgs : List VName → Expr.Args → List (VName × Expr) :=
  fun xs args => match xs, args with
  | [], _ => []
  | _, .nil => []
  | x :: xtl, .cons h ttl => (x, h) :: zipArgs xtl ttl

/-- Typing context mapping each variable to an optional class (Lecture #30). -/
abbrev Ctx := VName → Option CName

mutual
  /-- Expression typing (T-VAR/T-FIELD/T-INVK/T-NEW/T-UCAST/T-DCAST/T-SCAST). -/
  inductive Typing (ct : ClassTable) : Ctx → Expr → CName → Prop where
  | var {Γ : Ctx} {x : VName} {C : CName} :
    Γ x = some C → Typing ct Γ (.var x) C
  | field {Γ : Ctx} {e : Expr} {C Ci : CName} {f : FName}
    {fs : List (CName × FName)} :
    Typing ct Γ e C → fields ct C = some fs → (Ci, f) ∈ fs →
    Typing ct Γ (.fld e f) Ci
  | invk {Γ : Ctx} {e : Expr} {C B0 : CName} {m : MName}
    {args : Expr.Args} {Bs : List CName} :
    Typing ct Γ e C → mtype ct m C = some (Bs, B0) →
    ArgsTyping ct Γ args Bs → Typing ct Γ (.invk e m args) B0
  | new {Γ : Ctx} {C : CName} {args : Expr.Args}
    {fs : List (CName × FName)} :
    fields ct C = some fs →
    ArgsTyping ct Γ args (fs.map Prod.fst) →
    Typing ct Γ (.new C args) C
  | ucast {Γ : Ctx} {e : Expr} {D C : CName} :
    Typing ct Γ e D → Subtype ct D C → Typing ct Γ (.cast C e) C
  | dcast {Γ : Ctx} {e : Expr} {D C : CName} :
    Typing ct Γ e D → Subtype ct C D → C ≠ D →
    Typing ct Γ (.cast C e) C
  | scast {Γ : Ctx} {e : Expr} {D C : CName} :
    Typing ct Γ e D → ¬ Subtype ct C D → ¬ Subtype ct D C →
    Typing ct Γ (.cast C e) C

  /-- Argument typing for invocations and new (T-INVK/T-NEW helper). -/
  inductive ArgsTyping (ct : ClassTable) : Ctx → Expr.Args → List CName → Prop where
  | nil {Γ : Ctx} : ArgsTyping ct Γ .nil []
  | cons {Γ : Ctx} {e : Expr} {args : Expr.Args} {A B : CName}
    {Bs : List CName} :
    Typing ct Γ e A → Subtype ct A B → ArgsTyping ct Γ args Bs →
    ArgsTyping ct Γ (.cons e args) (B :: Bs)
end

/-- Context with this and params (helper for METHOD-OK). -/
def contextOf (C : CName) (params : List (CName × VName)) : Ctx :=
  fun x => if x = thisVar then some C
    else (params.find? (fun p => p.2 == x)).map Prod.fst

/-- Method well-formedness for an arbitrary class declaration and named method: body typing and
override (METHOD-OK); membership of the method in the class is checked by `ClassOk`. -/
def MethodOk (ct : ClassTable) (cd : ClassDecl) (p : MName × MethodDecl) :
    Prop :=
  (∃ A, Typing ct (contextOf cd.name p.2.params) p.2.body A ∧
    Subtype ct A p.2.ret) ∧
  override ct p.1 cd.super (p.2.params.map Prod.fst, p.2.ret)

/-- Class well-formedness: ctor and methods (CLASS-OK). -/
def ClassOk (ct : ClassTable) (cd : ClassDecl) : Prop :=
  (∃ fs, fields ct cd.super = some fs ∧
    cd.ctorParams = fs ++ cd.fields) ∧
  ∀ p ∈ cd.methods, MethodOk ct cd p

/-- Every class declaration of the table satisfies `ClassOk` (CLASS-OK). -/
def TableOk (ct : ClassTable) : Prop :=
  ∀ cd ∈ ct, ClassOk ct cd

/-- Valid class table: `WellFormed` and `TableOk` (Lecture #30 program check). -/
def ValidTable (ct : ClassTable) : Prop :=
  WellFormed ct ∧ TableOk ct

mutual
  /-- Single-step reduction (E-CONTEXT/E-PROJ/E-INVK/E-CAST). -/
  inductive Step (ct : ClassTable) : Expr → Expr → Prop where
  | proj {C : CName} {args : Expr.Args} {fs : List (CName × FName)}
    {f : FName} {v : Expr} :
    ArgsValue args → fields ct C = some fs →
    fieldValue fs args f = some v →
    Step ct (.fld (.new C args) f) v
  | invk {C : CName} {vs us : Expr.Args} {m : MName} {xs : List VName}
    {e : Expr} :
    ArgsValue vs → ArgsValue us → mbody ct m C = some (xs, e) →
    xs.length = Expr.Args.length us →
    Step ct (.invk (.new C vs) m us)
      (substMany ((thisVar, .new C vs) :: zipArgs xs us) e)
  | cast {C D : CName} {vs : Expr.Args} :
    ArgsValue vs → Subtype ct C D →
    Step ct (.cast D (.new C vs)) (.new C vs)
  | fldCongr {e e' : Expr} {f : FName} :
    Step ct e e' → Step ct (.fld e f) (.fld e' f)
  | invkRecv {e e' : Expr} {m : MName} {args : Expr.Args} :
    Step ct e e' → Step ct (.invk e m args) (.invk e' m args)
  | invkArgs {C : CName} {vs args args' : Expr.Args} {m : MName} :
    ArgsValue vs → ArgsStep ct args args' →
    Step ct (.invk (.new C vs) m args) (.invk (.new C vs) m args')
  | newArgs {C : CName} {args args' : Expr.Args} :
    ArgsStep ct args args' → Step ct (.new C args) (.new C args')
  | castCongr {C : CName} {e e' : Expr} :
    Step ct e e' → Step ct (.cast C e) (.cast C e')

  /-- Argument-list stepping (E-CONTEXT): the head steps with the tail unchanged, or the head is a
  value and the tail steps. -/
  inductive ArgsStep (ct : ClassTable) : Expr.Args → Expr.Args → Prop where
  | head {e e' : Expr} {args : Expr.Args} :
    Step ct e e' → ArgsStep ct (.cons e args) (.cons e' args)
  | tail {v : Expr} {args args' : Expr.Args} :
    Value v → ArgsStep ct args args' →
    ArgsStep ct (.cons v args) (.cons v args')
end

/-- Multi-step evaluation via reflexive-transitive closure (helper). -/
def Steps (ct : ClassTable) : Expr → Expr → Prop :=
  Relation.ReflTransGen (Step ct)

/-- Superclass chain length is bounded by table size (helper). -/
theorem supers_length_le (ct : ClassTable) (C : CName) :
    (supers ct C).length ≤ ct.length + 1 := by
  have h : ∀ (fuel : Nat) (C : CName),
      (supersAux ct fuel C).length ≤ fuel := by
    intro fuel
    induction fuel with
    | zero =>
      intro C
      simp [supersAux]
    | succ fuel ih =>
      intro C
      simp only [supersAux]
      by_cases hC : C = Object
      · rw [ite_eq_left hC]
        simp only [List.length_cons, List.length_nil]
        omega
      · rw [ite_eq_right hC]
        cases hlk : lookupClass ct C
        case none =>
          simp only [List.length_cons, List.length_nil]
          omega
        case some =>
          rename_i cd
          simp only [List.length_cons]
          have hle := ih cd.super
          omega
  exact h (ct.length + 1) C

/-- Fields of Object are empty (F-OBJECT). -/
theorem fields_object (ct : ClassTable) :
    fields ct Object = some [] := by
  simp [fields]

/-- Fields extend super fields with own fields (F-CLASS). -/
theorem fields_step {ct : ClassTable} (h : WellFormed ct) {C : CName}
    {cd : ClassDecl} {fs : List (CName × FName)} : C ≠ Object →
    lookupClass ct C = some cd → fields ct cd.super = some fs →
    fields ct C = some (fs ++ cd.fields) := by
  intro hCne hlk hfs
  have hmem : cd ∈ ct := List.mem_of_find?_eq_some hlk
  have hpred : (cd.name == C) = true :=
    List.find?_some (p := fun (cd : ClassDecl) => cd.name == C) hlk
  have hname : cd.name = C := beq_iff_eq.mp hpred
  have hU : supers ct C = C :: supersAux ct ct.length cd.super := by
    simp only [supers, supersAux]
    rw [ite_eq_right hCne, hlk]
  have hF : ∀ (n : Nat) (X : CName),
      supersAux ct n X = supersAux ct (n + 1) X ∨
      ((supersAux ct n X).length = n ∧
        ∀ Y ∈ supersAux ct n X, ∃ d, lookupClass ct Y = some d) := by
    intro n
    induction n with
    | zero =>
      intro X
      right
      constructor
      · rfl
      · intro Y hY
        simp only [supersAux, List.not_mem_nil] at hY
    | succ n ih =>
      intro X
      by_cases hX : X = Object
      · have e1 : supersAux ct (n + 1) X = [Object] := by
          simp only [supersAux]
          rw [ite_eq_left hX]
        have e2 : supersAux ct (n + 1 + 1) X = [Object] := by
          simp only [supersAux]
          rw [ite_eq_left hX]
        left
        rw [e1, e2]
      · cases hlkX : lookupClass ct X
        · have e1 : supersAux ct (n + 1) X = [X] := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have e2 : supersAux ct (n + 1 + 1) X = [X] := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          left
          rw [e1, e2]
        · rename_i d
          have e1 : supersAux ct (n + 1) X =
              X :: supersAux ct n d.super := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have e2 : supersAux ct (n + 1 + 1) X =
              X :: supersAux ct (n + 1) d.super := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have ihd := ih d.super
          cases ihd with
          | inl heq =>
            left
            rw [e1, e2, heq]
          | inr hlen =>
            have hlen1 : (supersAux ct n d.super).length = n :=
              hlen.1
            have hall : ∀ Y ∈ supersAux ct n d.super,
                ∃ d, lookupClass ct Y = some d := hlen.2
            right
            constructor
            · rw [e1, List.length_cons, hlen1]
            · intro Y hY
              rw [e1] at hY
              have hY := List.mem_cons.mp hY
              cases hY with
              | inl heq =>
                subst heq
                exact ⟨d, hlkX⟩
              | inr hmem2 =>
                exact hall Y hmem2
  have hS : supersAux ct ct.length cd.super =
      supersAux ct (ct.length + 1) cd.super := by
    have hinst := hF ct.length cd.super
    cases hinst with
    | inl heq =>
      exact heq
    | inr hlen =>
      exfalso
      have hNodup0 : (supers ct cd.name).Nodup :=
        h.supersNodup cd hmem
      rw [hname] at hNodup0
      rw [hU] at hNodup0
      have hsub : (C :: supersAux ct ct.length cd.super) ⊆
          ct.map ClassDecl.name := by
        intro Y hY
        have hY := List.mem_cons.mp hY
        cases hY with
        | inl heq =>
          subst heq
          have hm : cd.name ∈ ct.map ClassDecl.name :=
            List.mem_map_of_mem hmem
          rw [hname] at hm
          exact hm
        | inr hmem2 =>
          have hex := hlen.2 Y hmem2
          cases hex with
          | intro d hd =>
            have hdm : d ∈ ct := List.mem_of_find?_eq_some hd
            have hdpred : (d.name == Y) = true :=
              List.find?_some (p := fun (cd : ClassDecl) => cd.name == Y) hd
            have hdname : d.name = Y := beq_iff_eq.mp hdpred
            have hm : d.name ∈ ct.map ClassDecl.name :=
              List.mem_map_of_mem hdm
            rw [hdname] at hm
            exact hm
      have hle := List.Nodup.length_le_of_subset hNodup0 hsub
      have hmaplen : (ct.map ClassDecl.name).length = ct.length :=
        List.length_map ClassDecl.name
      rw [hmaplen] at hle
      have hlen1 : (supersAux ct ct.length cd.super).length =
          ct.length := hlen.1
      have hlong : (C :: supersAux ct ct.length cd.super).length =
          ct.length + 1 := by
        simp only [List.length_cons, hlen1]
      omega
  have hShape : supers ct C = C :: supers ct cd.super := by
    rw [hU, hS]
    simp only [supers]
  have hnone : ∀ (L : List CName),
      List.foldl (fun (acc : Option (List (CName × FName))) (D : CName) =>
        match acc with
        | none => none
        | some ys =>
          if D = Object then some ys
          else match lookupClass ct D with
          | none => none
          | some d => some (d.fields ++ ys)) none L = none := by
    intro L
    induction L with
    | nil =>
      simp only [List.foldl_nil]
    | cons D Ds ih =>
      simp only [List.foldl_cons, ih]
  have hdist : ∀ (L : List CName) (xs : List (CName × FName)),
      List.foldl (fun (acc : Option (List (CName × FName))) (D : CName) =>
        match acc with
        | none => none
        | some ys =>
          if D = Object then some ys
          else match lookupClass ct D with
          | none => none
          | some d => some (d.fields ++ ys)) (some xs) L =
        match List.foldl (fun (acc : Option (List (CName × FName)))
          (D : CName) => match acc with
          | none => none
          | some ys =>
            if D = Object then some ys
            else match lookupClass ct D with
            | none => none
            | some d => some (d.fields ++ ys)) (some []) L with
        | none => none
        | some ys0 => some (ys0 ++ xs) := by
    intro L
    induction L with
    | nil =>
      intro xs
      simp only [List.foldl_nil, List.nil_append]
    | cons D Ds ih =>
      intro xs
      simp only [List.foldl_cons]
      by_cases hD : D = Object
      · simp only [ite_eq_left hD]
        exact ih xs
      · cases hlkD : lookupClass ct D
        · simp only [ite_eq_right hD, hnone]
        · rename_i d
          simp only [ite_eq_right hD]
          have h1 := ih (d.fields ++ xs)
          have h2 := ih (d.fields ++ [])
          rw [h1, h2]
          cases h0 : List.foldl
            (fun (acc : Option (List (CName × FName))) (D : CName) =>
              match acc with
              | none => none
              | some ys =>
                if D = Object then some ys
                else match lookupClass ct D with
                | none => none
                | some d => some (d.fields ++ ys)) (some []) Ds
          · rfl
          · rename_i ys0
            simp only [List.append_nil, List.append_assoc]
  by_cases hsup : cd.super = Object
  · have hobj := fields_object ct
    rw [hsup] at hfs
    rw [hobj] at hfs
    have heq : ([] : List (CName × FName)) = fs := by
      injection hfs
    subst heq
    simp only [List.nil_append]
    have hsupobj : supers ct Object = [Object] := by
      simp only [supers, supersAux]
      rfl
    have hCeq : fields ct C =
        List.foldl (fun (acc : Option (List (CName × FName))) (D : CName) =>
          match acc with
          | none => none
          | some ys =>
            if D = Object then some ys
            else match lookupClass ct D with
            | none => none
            | some d => some (d.fields ++ ys)) (some [])
          (supers ct C) := by
      simp only [fields, ite_eq_right hCne]
    rw [hCeq, hShape, hsup, hsupobj]
    simp only [List.foldl_cons, List.foldl_nil, ite_eq_right hCne, hlk]
    simp only [List.append_nil]
    rfl
  · have hCeq : fields ct C =
        List.foldl (fun (acc : Option (List (CName × FName))) (D : CName) =>
          match acc with
          | none => none
          | some ys =>
            if D = Object then some ys
            else match lookupClass ct D with
            | none => none
            | some d => some (d.fields ++ ys)) (some [])
          (supers ct C) := by
      simp only [fields, ite_eq_right hCne]
    have hfs2 : List.foldl
        (fun (acc : Option (List (CName × FName))) (D : CName) =>
          match acc with
          | none => none
          | some ys =>
            if D = Object then some ys
            else match lookupClass ct D with
            | none => none
            | some d => some (d.fields ++ ys)) (some [])
        (supers ct cd.super) = some fs := by
      have hz := hfs
      simp only [fields, ite_eq_right hsup] at hz
      exact hz
    rw [hCeq, hShape, List.foldl_cons]
    simp only [ite_eq_right hCne, hlk]
    have hdistS := hdist (supers ct cd.super) cd.fields
    simp only [hfs2] at hdistS
    simp only [List.append_nil]
    exact hdistS

/-- Method type finds locally defined method (MT-CLASS). -/
theorem mtype_step_some {ct : ClassTable} (h : WellFormed ct) {C : CName}
    {cd : ClassDecl} {m : MName} {md : MethodDecl} :
    lookupClass ct C = some cd → (m, md) ∈ cd.methods →
    mtype ct m C = some (md.params.map Prod.fst, md.ret) := by
  intro hlk hmem0
  have hK : ∀ (α : Type) (l : List (MName × α)) (m : MName) (md : α),
      (l.map Prod.fst).Nodup → (m, md) ∈ l →
      (l.find? fun p => p.1 == m) = some (m, md) := by
    intro α l
    induction l with
    | nil =>
      intro m md _ hmem
      exact absurd hmem List.not_mem_nil
    | cons hd tl ih =>
      intro m md hnodup hmem
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hne : hd.1 ∉ tl.map Prod.fst := hnodup.1
      have htl : (tl.map Prod.fst).Nodup := hnodup.2
      have hmem2 := List.mem_cons.mp hmem
      cases hmem2 with
      | inl heq =>
        subst heq
        have h1 : List.find? (fun p : MName × α => p.1 == m)
            ((m, md) :: tl) = match m == m with
            | true => some (m, md)
            | false => List.find? (fun p : MName × α => p.1 == m) tl :=
          List.find?_cons
        rw [h1, beq_self_eq_true]
      | inr hmem3 =>
        have hmtail : m ∈ tl.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hmem3
        have hne2 : hd.1 ≠ m := by
          intro hcon
          rw [← hcon] at hmtail
          exact hne hmtail
        have hcond : (hd.1 == m) = false := by
          cases h2 : hd.1 == m
          case true =>
            exact absurd (beq_iff_eq.mp h2) hne2
          case false =>
            rfl
        have h1 : List.find? (fun p : MName × α => p.1 == m) (hd :: tl) =
            match hd.1 == m with
            | true => some hd
            | false => List.find? (fun p : MName × α => p.1 == m) tl :=
          List.find?_cons
        rw [h1, hcond]
        exact ih m md htl hmem3
  have hmem : cd ∈ ct := List.mem_of_find?_eq_some hlk
  have hpred : (cd.name == C) = true :=
    List.find?_some (p := fun (cd : ClassDecl) => cd.name == C) hlk
  have hname : cd.name = C := beq_iff_eq.mp hpred
  have hObj : cd.name ≠ Object := h.objectUndeclared cd hmem
  have hCne : C ≠ Object := by
    intro hCO
    exact hObj (hname.trans hCO)
  have hU : supers ct C = C :: supersAux ct ct.length cd.super := by
    simp only [supers, supersAux]
    rw [ite_eq_right hCne, hlk]
  have hnodup : (cd.methods.map Prod.fst).Nodup :=
    h.methodNamesNodup cd hmem
  have hfind : (cd.methods.find? fun p => p.1 == m) = some (m, md) :=
    hK MethodDecl cd.methods m md hnodup hmem0
  have hhead : (if C = Object then (none : Option MethodDecl) else
      (lookupClass ct C).bind fun cd =>
        (cd.methods.find? fun p => p.1 == m).map Prod.snd) = some md := by
    simp only [ite_eq_right hCne, hlk, Option.bind_some, hfind,
      Option.map_some]
  have hLM : lookupMethod ct m C = some md := by
    simp only [lookupMethod, hU, List.findSome?_cons, hhead]
  simp only [mtype, hLM, Option.map_some]

/-- Method type recurses to superclass when missing (MT-SUPER). -/
theorem mtype_step_none {ct : ClassTable} (h : WellFormed ct) {C : CName}
    {cd : ClassDecl} {m : MName} : lookupClass ct C = some cd →
    (∀ p ∈ cd.methods, p.1 ≠ m) → mtype ct m C = mtype ct m cd.super := by
  intro hlk hnone
  have hmem : cd ∈ ct := List.mem_of_find?_eq_some hlk
  have hpred : (cd.name == C) = true :=
    List.find?_some (p := fun (cd : ClassDecl) => cd.name == C) hlk
  have hname : cd.name = C := beq_iff_eq.mp hpred
  have hObj : cd.name ≠ Object := h.objectUndeclared cd hmem
  have hCne : C ≠ Object := by
    intro hCO
    exact hObj (hname.trans hCO)
  have hU : supers ct C = C :: supersAux ct ct.length cd.super := by
    simp only [supers, supersAux]
    rw [ite_eq_right hCne, hlk]
  have hF : ∀ (n : Nat) (X : CName),
      supersAux ct n X = supersAux ct (n + 1) X ∨
      ((supersAux ct n X).length = n ∧
        ∀ Y ∈ supersAux ct n X, ∃ d, lookupClass ct Y = some d) := by
    intro n
    induction n with
    | zero =>
      intro X
      right
      constructor
      · simp [supersAux]
      · intro Y hY
        simp [supersAux] at hY
    | succ n ih =>
      intro X
      by_cases hX : X = Object
      · have e1 : supersAux ct (n + 1) X = [Object] := by
          simp only [supersAux]
          rw [ite_eq_left hX]
        have e2 : supersAux ct (n + 1 + 1) X = [Object] := by
          simp only [supersAux]
          rw [ite_eq_left hX]
        left
        rw [e1, e2]
      · cases hlkX : lookupClass ct X
        · have e1 : supersAux ct (n + 1) X = [X] := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have e2 : supersAux ct (n + 1 + 1) X = [X] := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          left
          rw [e1, e2]
        · rename_i d
          have e1 : supersAux ct (n + 1) X =
              X :: supersAux ct n d.super := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have e2 : supersAux ct (n + 1 + 1) X =
              X :: supersAux ct (n + 1) d.super := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have ihd := ih d.super
          cases ihd with
          | inl heq =>
            left
            rw [e1, e2, heq]
          | inr hlen =>
            have hlen1 : (supersAux ct n d.super).length = n :=
              hlen.1
            have hall : ∀ Y ∈ supersAux ct n d.super,
                ∃ d, lookupClass ct Y = some d := hlen.2
            right
            constructor
            · rw [e1, List.length_cons, hlen1]
            · intro Y hY
              rw [e1] at hY
              have hY := List.mem_cons.mp hY
              cases hY with
              | inl heq =>
                subst heq
                exact ⟨d, hlkX⟩
              | inr hmem2 =>
                exact hall Y hmem2
  have hS : supersAux ct ct.length cd.super =
      supersAux ct (ct.length + 1) cd.super := by
    have hinst := hF ct.length cd.super
    cases hinst with
    | inl heq =>
      exact heq
    | inr hlen =>
      exfalso
      have hNodup0 : (supers ct cd.name).Nodup :=
        h.supersNodup cd hmem
      rw [hname] at hNodup0
      rw [hU] at hNodup0
      have hsub : (C :: supersAux ct ct.length cd.super) ⊆
          ct.map ClassDecl.name := by
        intro Y hY
        have hY := List.mem_cons.mp hY
        cases hY with
        | inl heq =>
          subst heq
          have hm : cd.name ∈ ct.map ClassDecl.name :=
            List.mem_map_of_mem hmem
          rw [hname] at hm
          exact hm
        | inr hmem2 =>
          have hex := hlen.2 Y hmem2
          cases hex with
          | intro d hd =>
            have hdm : d ∈ ct := List.mem_of_find?_eq_some hd
            have hdpred : (d.name == Y) = true :=
              List.find?_some (p := fun (cd : ClassDecl) => cd.name == Y) hd
            have hdname : d.name = Y := beq_iff_eq.mp hdpred
            have hm : d.name ∈ ct.map ClassDecl.name :=
              List.mem_map_of_mem hdm
            rw [hdname] at hm
            exact hm
      have hle := List.Nodup.length_le_of_subset hNodup0 hsub
      have hmaplen : (ct.map ClassDecl.name).length = ct.length :=
        List.length_map ClassDecl.name
      rw [hmaplen] at hle
      have hlen1 : (supersAux ct ct.length cd.super).length =
          ct.length := hlen.1
      have hlong : (C :: supersAux ct ct.length cd.super).length =
          ct.length + 1 := by
        simp only [List.length_cons, hlen1]
      omega
  have hShape : supers ct C = C :: supers ct cd.super := by
    rw [hU, hS]
    simp only [supers]
  have hfindnone : cd.methods.find? (fun p => p.1 == m) = none := by
    rw [List.find?_eq_none]
    intro x hx htrue
    have hne : x.1 ≠ m := hnone x hx
    have heq : x.1 = m := beq_iff_eq.mp htrue
    exact hne heq
  have hhead : (if C = Object then (none : Option MethodDecl) else
      (lookupClass ct C).bind fun cd =>
        (cd.methods.find? fun p => p.1 == m).map Prod.snd) = none := by
    simp only [ite_eq_right hCne, hlk, Option.bind_some, hfindnone,
      Option.map_none]
  have hLM : lookupMethod ct m C = lookupMethod ct m cd.super := by
    simp only [lookupMethod, hShape, List.findSome?_cons, hhead]
  simp only [mtype, hLM]

/-- Method body finds locally defined method (MB-CLASS). -/
theorem mbody_step_some {ct : ClassTable} (h : WellFormed ct) {C : CName}
    {cd : ClassDecl} {m : MName} {md : MethodDecl} :
    lookupClass ct C = some cd → (m, md) ∈ cd.methods →
    mbody ct m C = some (md.params.map Prod.snd, md.body) := by
  intro hlk hmem0
  have hK : ∀ (α : Type) (l : List (MName × α)) (m : MName) (md : α),
      (l.map Prod.fst).Nodup → (m, md) ∈ l →
      (l.find? fun p => p.1 == m) = some (m, md) := by
    intro α l
    induction l with
    | nil =>
      intro m md _ hmem
      exact absurd hmem List.not_mem_nil
    | cons hd tl ih =>
      intro m md hnodup hmem
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hne : hd.1 ∉ tl.map Prod.fst := hnodup.1
      have htl : (tl.map Prod.fst).Nodup := hnodup.2
      have hmem2 := List.mem_cons.mp hmem
      cases hmem2 with
      | inl heq =>
        subst heq
        have h1 : List.find? (fun p : MName × α => p.1 == m)
            ((m, md) :: tl) = match m == m with
            | true => some (m, md)
            | false => List.find? (fun p : MName × α => p.1 == m) tl :=
          List.find?_cons
        rw [h1, beq_self_eq_true]
      | inr hmem3 =>
        have hmtail : m ∈ tl.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hmem3
        have hne2 : hd.1 ≠ m := by
          intro hcon
          rw [← hcon] at hmtail
          exact hne hmtail
        have hcond : (hd.1 == m) = false := by
          cases h2 : hd.1 == m
          case true =>
            exact absurd (beq_iff_eq.mp h2) hne2
          case false =>
            rfl
        have h1 : List.find? (fun p : MName × α => p.1 == m) (hd :: tl) =
            match hd.1 == m with
            | true => some hd
            | false => List.find? (fun p : MName × α => p.1 == m) tl :=
          List.find?_cons
        rw [h1, hcond]
        exact ih m md htl hmem3
  have hmem : cd ∈ ct := List.mem_of_find?_eq_some hlk
  have hpred : (cd.name == C) = true :=
    List.find?_some (p := fun (cd : ClassDecl) => cd.name == C) hlk
  have hname : cd.name = C := beq_iff_eq.mp hpred
  have hObj : cd.name ≠ Object := h.objectUndeclared cd hmem
  have hCne : C ≠ Object := by
    intro hCO
    exact hObj (hname.trans hCO)
  have hU : supers ct C = C :: supersAux ct ct.length cd.super := by
    simp only [supers, supersAux]
    rw [ite_eq_right hCne, hlk]
  have hnodup : (cd.methods.map Prod.fst).Nodup :=
    h.methodNamesNodup cd hmem
  have hfind : (cd.methods.find? fun p => p.1 == m) = some (m, md) :=
    hK MethodDecl cd.methods m md hnodup hmem0
  have hhead : (if C = Object then (none : Option MethodDecl) else
      (lookupClass ct C).bind fun cd =>
        (cd.methods.find? fun p => p.1 == m).map Prod.snd) = some md := by
    simp only [ite_eq_right hCne, hlk, Option.bind_some, hfind,
      Option.map_some]
  have hLM : lookupMethod ct m C = some md := by
    simp only [lookupMethod, hU, List.findSome?_cons, hhead]
  simp only [mbody, hLM, Option.map_some]

/-- Method body recurses to superclass when missing (MB-SUPER). -/
theorem mbody_step_none {ct : ClassTable} (h : WellFormed ct) {C : CName}
    {cd : ClassDecl} {m : MName} : lookupClass ct C = some cd →
    (∀ p ∈ cd.methods, p.1 ≠ m) → mbody ct m C = mbody ct m cd.super := by
  intro hlk hnone
  have hmem : cd ∈ ct := List.mem_of_find?_eq_some hlk
  have hpred : (cd.name == C) = true :=
    List.find?_some (p := fun (cd : ClassDecl) => cd.name == C) hlk
  have hname : cd.name = C := beq_iff_eq.mp hpred
  have hObj : cd.name ≠ Object := h.objectUndeclared cd hmem
  have hCne : C ≠ Object := by
    intro hCO
    exact hObj (hname.trans hCO)
  have hU : supers ct C = C :: supersAux ct ct.length cd.super := by
    simp only [supers, supersAux]
    rw [ite_eq_right hCne, hlk]
  have hF : ∀ (n : Nat) (X : CName),
      supersAux ct n X = supersAux ct (n + 1) X ∨
      ((supersAux ct n X).length = n ∧
        ∀ Y ∈ supersAux ct n X, ∃ d, lookupClass ct Y = some d) := by
    intro n
    induction n with
    | zero =>
      intro X
      right
      constructor
      · simp [supersAux]
      · intro Y hY
        simp [supersAux] at hY
    | succ n ih =>
      intro X
      by_cases hX : X = Object
      · have e1 : supersAux ct (n + 1) X = [Object] := by
          simp only [supersAux]
          rw [ite_eq_left hX]
        have e2 : supersAux ct (n + 1 + 1) X = [Object] := by
          simp only [supersAux]
          rw [ite_eq_left hX]
        left
        rw [e1, e2]
      · cases hlkX : lookupClass ct X
        · have e1 : supersAux ct (n + 1) X = [X] := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have e2 : supersAux ct (n + 1 + 1) X = [X] := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          left
          rw [e1, e2]
        · rename_i d
          have e1 : supersAux ct (n + 1) X =
              X :: supersAux ct n d.super := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have e2 : supersAux ct (n + 1 + 1) X =
              X :: supersAux ct (n + 1) d.super := by
            simp only [supersAux]
            rw [ite_eq_right hX, hlkX]
          have ihd := ih d.super
          cases ihd with
          | inl heq =>
            left
            rw [e1, e2, heq]
          | inr hlen =>
            have hlen1 : (supersAux ct n d.super).length = n :=
              hlen.1
            have hall : ∀ Y ∈ supersAux ct n d.super,
                ∃ d, lookupClass ct Y = some d := hlen.2
            right
            constructor
            · rw [e1, List.length_cons, hlen1]
            · intro Y hY
              rw [e1] at hY
              have hY := List.mem_cons.mp hY
              cases hY with
              | inl heq =>
                subst heq
                exact ⟨d, hlkX⟩
              | inr hmem2 =>
                exact hall Y hmem2
  have hS : supersAux ct ct.length cd.super =
      supersAux ct (ct.length + 1) cd.super := by
    have hinst := hF ct.length cd.super
    cases hinst with
    | inl heq =>
      exact heq
    | inr hlen =>
      exfalso
      have hNodup0 : (supers ct cd.name).Nodup :=
        h.supersNodup cd hmem
      rw [hname] at hNodup0
      rw [hU] at hNodup0
      have hsub : (C :: supersAux ct ct.length cd.super) ⊆
          ct.map ClassDecl.name := by
        intro Y hY
        have hY := List.mem_cons.mp hY
        cases hY with
        | inl heq =>
          subst heq
          have hm : cd.name ∈ ct.map ClassDecl.name :=
            List.mem_map_of_mem hmem
          rw [hname] at hm
          exact hm
        | inr hmem2 =>
          have hex := hlen.2 Y hmem2
          cases hex with
          | intro d hd =>
            have hdm : d ∈ ct := List.mem_of_find?_eq_some hd
            have hdpred : (d.name == Y) = true :=
              List.find?_some (p := fun (cd : ClassDecl) => cd.name == Y) hd
            have hdname : d.name = Y := beq_iff_eq.mp hdpred
            have hm : d.name ∈ ct.map ClassDecl.name :=
              List.mem_map_of_mem hdm
            rw [hdname] at hm
            exact hm
      have hle := List.Nodup.length_le_of_subset hNodup0 hsub
      have hmaplen : (ct.map ClassDecl.name).length = ct.length :=
        List.length_map ClassDecl.name
      rw [hmaplen] at hle
      have hlen1 : (supersAux ct ct.length cd.super).length =
          ct.length := hlen.1
      have hlong : (C :: supersAux ct ct.length cd.super).length =
          ct.length + 1 := by
        simp only [List.length_cons, hlen1]
      omega
  have hShape : supers ct C = C :: supers ct cd.super := by
    rw [hU, hS]
    simp only [supers]
  have hfindnone : cd.methods.find? (fun p => p.1 == m) = none := by
    rw [List.find?_eq_none]
    intro x hx htrue
    have hne : x.1 ≠ m := hnone x hx
    have heq : x.1 = m := beq_iff_eq.mp htrue
    exact hne heq
  have hhead : (if C = Object then (none : Option MethodDecl) else
      (lookupClass ct C).bind fun cd =>
        (cd.methods.find? fun p => p.1 == m).map Prod.snd) = none := by
    simp only [ite_eq_right hCne, hlk, Option.bind_some, hfindnone,
      Option.map_none]
  have hLM : lookupMethod ct m C = lookupMethod ct m cd.super := by
    simp only [lookupMethod, hShape, List.findSome?_cons, hhead]
  simp only [mbody, hLM]

/-- Single-step reduction is deterministic (helper). -/
theorem Step.deterministic {ct : ClassTable}
    {e e1 e2 : Expr} : Step ct e e1 → Step ct e e2 → e1 = e2 := by
  have noStep : ∀ {e e' : Expr}, Value e → Step ct e e' → False := by
    intro e e' hv hs
    refine Value.rec (motive_1 := fun e _ => ∀ e', Step ct e e' → False)
      (motive_2 := fun a _ => ∀ a', ArgsStep ct a a' → False) ?_ ?_ ?_ hv e' hs
    · intro C args hav ih e' hs
      cases hs with
      | newArgs st => exact ih _ st
    · intro a' hs
      cases hs
    · intro head tail hv ht ih1 ih2 a' hs
      cases hs with
      | head st => exact ih1 _ st
      | tail _ st => exact ih2 _ st
  have noArgsStep : ∀ {a a' : Expr.Args}, ArgsValue a → ArgsStep ct a a' → False := by
    intro a a' hv hs
    refine ArgsValue.rec (motive_1 := fun e _ => ∀ e', Step ct e e' → False)
      (motive_2 := fun a _ => ∀ a', ArgsStep ct a a' → False) ?_ ?_ ?_ hv a' hs
    · intro C args hav ih e' hs
      cases hs with
      | newArgs st => exact ih _ st
    · intro a' hs
      cases hs
    · intro head tail hv ht ih1 ih2 a' hs
      cases hs with
      | head st => exact ih1 _ st
      | tail _ st => exact ih2 _ st
  intro h1 h2
  refine Step.rec (motive_1 := fun e e1 _ => ∀ e2, Step ct e e2 → e1 = e2)
    (motive_2 := fun a a1 _ => ∀ a2, ArgsStep ct a a2 → a1 = a2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h1 e2 h2
  · intro C args fs f v hav hfld hfv e2' h2'
    cases h2' with
    | proj _ hf' hfv' =>
      rw [hfld] at hf'
      injection hf' with hfs
      subst hfs
      rw [hfv] at hfv'
      injection hfv' with heq
    | fldCongr st =>
      exact (noStep (Value.new C args hav) st).elim
  · intro C vs us m xs e hvs hus hmbody hlen e2' h2'
    cases h2' with
    | invk _ _ hm' _ =>
      rw [hmbody] at hm'
      injection hm' with hpair
      injection hpair with hxs he
      subst hxs
      subst he
      rfl
    | invkRecv st =>
      exact (noStep (Value.new C vs hvs) st).elim
    | invkArgs _ st =>
      exact (noArgsStep hus st).elim
  · intro C D vs hvs hsub e2' h2'
    cases h2' with
    | cast _ _ => rfl
    | castCongr st =>
      exact (noStep (Value.new C vs hvs) st).elim
  · intro e e' f st ih e2' h2'
    cases h2' with
    | proj hv' _ _ =>
      exact (noStep (Value.new _ _ hv') st).elim
    | fldCongr st' =>
      have heq := ih _ st'
      rw [heq]
  · intro e e' m args st ih e2' h2'
    cases h2' with
    | invk hvs' _ _ _ =>
      exact (noStep (Value.new _ _ hvs') st).elim
    | invkRecv st' =>
      have heq := ih _ st'
      rw [heq]
    | invkArgs hvs' _ =>
      exact (noStep (Value.new _ _ hvs') st).elim
  · intro C vs args args' m hvs st ih e2' h2'
    cases h2' with
    | invk _ hus' _ _ =>
      exact (noArgsStep hus' st).elim
    | invkRecv st' =>
      exact (noStep (Value.new C vs hvs) st').elim
    | invkArgs _ st' =>
      have heq := ih _ st'
      rw [heq]
  · intro C args args' st ih e2' h2'
    cases h2' with
    | newArgs st' =>
      have heq := ih _ st'
      rw [heq]
  · intro C e e' st ih e2' h2'
    cases h2' with
    | cast hvs' _ =>
      exact (noStep (Value.new _ _ hvs') st).elim
    | castCongr st' =>
      have heq := ih _ st'
      rw [heq]
  · intro e e' args st ih a2' h2'
    cases h2' with
    | head st' =>
      have heq := ih _ st'
      rw [heq]
    | tail hv' _ =>
      exact (noStep hv' st).elim
  · intro v args args' hv st ih a2' h2'
    cases h2' with
    | head st' =>
      exact (noStep hv st').elim
    | tail _ st' =>
      have heq := ih _ st'
      rw [heq]

end Cslib.FeatherweightJava
