/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.FeatherweightJava.Basic
public import Mathlib.Logic.Function.Basic

/-!
Structural lemmas for Featherweight Java type soundness: method-type and
method-body lookup, field extension under subtyping, weakening, term
substitution preserving typing up to subtyping, and method-body typing,
following Igarashi, Pierce and Wadler, *Featherweight Java* (TOPLAS 2001),
Appendix A.1, Lemmas A.1.1-A.1.4.
-/

@[expose] public section
set_option autoImplicit false
namespace Cslib.FeatherweightJava

/-- A defined method type comes with a method body of the same arity
(TOPLAS Thm 2.4.2 proof; AFP `mtype-mbody`). -/
theorem mtype_mbody {ct : ClassTable} {m : MName} {C : CName}
    {Bs : List CName} {B : CName} (h : mtype ct m C = some (Bs, B)) :
    ∃ xs e, mbody ct m C = some (xs, e) ∧ xs.length = Bs.length := by
  obtain ⟨md, hmd, heq⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at heq
  refine ⟨md.params.map Prod.snd, md.body, ?_, ?_⟩
  · simp only [mbody, hmd, Option.map_some]
  · rw [← heq.1, List.length_map, List.length_map]

/-- A declared class is found by its own name in a table with distinct class
names (helper for the subtype lemmas). -/
private theorem lookupClass_of_mem {ct : ClassTable}
    (hnd : (ct.map ClassDecl.name).Nodup) {cd : ClassDecl} (hmem : cd ∈ ct) :
    lookupClass ct cd.name = some cd := by
  unfold lookupClass
  induction ct with
  | nil => exact absurd hmem List.not_mem_nil
  | cons d tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hmem with rfl | htl
    · exact List.find?_cons_of_pos (p := fun c : ClassDecl => c.name == cd.name)
        (beq_self_eq_true _)
    · have hne : ¬ (d.name == cd.name) = true := by
        rw [beq_iff_eq]
        intro he
        exact hnd.1 (he ▸ List.mem_map_of_mem (f := ClassDecl.name) htl)
      rw [List.find?_cons_of_neg (p := fun c : ClassDecl => c.name == cd.name) hne]
      exact ih hnd.2 htl

/-- Method types are invariant down the subtype relation
(TOPLAS Lemma A.1.1; AFP `A-1-1`). -/
theorem mtype_of_subtype {ct : ClassTable} (hwf : WellFormed ct) {m : MName}
    {C D : CName} {Bs : List CName} {B : CName} (hsub : Subtype ct C D)
    (h : mtype ct m D = some (Bs, B)) :
    mtype ct m C = some (Bs, B) := by
  induction hsub using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hCE _ ih =>
    obtain ⟨cd, hmem, rfl, rfl⟩ := hCE
    have hlk := lookupClass_of_mem hwf.namesNodup hmem
    by_cases hm : ∃ md, (m, md) ∈ cd.methods
    · obtain ⟨md, hmd⟩ := hm
      rw [mtype_step_some hwf hlk hmd]
      exact congrArg some (hwf.overrideOk cd hmem (m, md) hmd _ ih).symm
    · rw [mtype_step_none hwf hlk (fun ⟨a, b⟩ hp hpm => hm ⟨b, hpm ▸ hp⟩)]
      exact ih

/-- Fields of a subclass extend the fields of its superclass
(TOPLAS Lemma A.1.2 proof, T-FIELD case; AFP `sub-fields`). -/
theorem fields_of_subtype {ct : ClassTable} (hwf : WellFormed ct)
    {C D : CName} {fs : List (CName × FName)} (hsub : Subtype ct C D)
    (h : fields ct D = some fs) :
    ∃ gs, fields ct C = some (fs ++ gs) := by
  induction hsub using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by rw [List.append_nil]; exact h⟩
  | head hCE _ ih =>
    obtain ⟨cd, hmem, rfl, rfl⟩ := hCE
    obtain ⟨gs, hgs⟩ := ih
    refine ⟨gs ++ cd.fields, ?_⟩
    rw [fields_step hwf (hwf.objectUndeclared cd hmem)
      (lookupClass_of_mem hwf.namesNodup hmem) hgs, List.append_assoc]

mutual
  /-- Weakening by context inclusion (TOPLAS Lemma A.1.3; AFP `A-1-3`). -/
  theorem Typing.weaken {ct : ClassTable} {Γ Γ' : Ctx} {e : Expr} {C : CName}
      (hΓ : ∀ x A, Γ x = some A → Γ' x = some A) (h : Typing ct Γ e C) :
      Typing ct Γ' e C :=
    match h with
    | .var hx => .var (hΓ _ _ hx)
    | .field he hf hm => .field (Typing.weaken hΓ he) hf hm
    | .invk he hm ha => .invk (Typing.weaken hΓ he) hm (ArgsTyping.weaken hΓ ha)
    | .new hf ha => .new hf (ArgsTyping.weaken hΓ ha)
    | .ucast he hs => .ucast (Typing.weaken hΓ he) hs
    | .dcast he hs hne => .dcast (Typing.weaken hΓ he) hs hne
    | .scast he h1 h2 => .scast (Typing.weaken hΓ he) h1 h2

  /-- Weakening for argument typing (TOPLAS Lemma A.1.3; AFP `A-1-3`). -/
  theorem ArgsTyping.weaken {ct : ClassTable} {Γ Γ' : Ctx} {args : Expr.Args}
      {Bs : List CName} (hΓ : ∀ x A, Γ x = some A → Γ' x = some A)
      (h : ArgsTyping ct Γ args Bs) :
      ArgsTyping ct Γ' args Bs :=
    match h with
    | .nil => .nil
    | .cons he hs ha => .cons (Typing.weaken hΓ he) hs (ArgsTyping.weaken hΓ ha)
end

/-- Weakening by one fresh binding, the literal form of TOPLAS Lemma A.1.3. -/
theorem Typing.weaken_update {ct : ClassTable} {Γ : Ctx} {x : VName}
    {D C : CName} {e : Expr} (hx : Γ x = none) (h : Typing ct Γ e C) :
    Typing ct (Function.update Γ x (some D)) e C := by
  refine Typing.weaken (fun y A hy => ?_) h
  by_cases hyx : y = x
  · subst hyx
    rw [hx] at hy
    exact absurd hy (by simp only [reduceCtorEq, not_false_eq_true])
  · rw [Function.update_of_ne hyx]
    exact hy

mutual
  /-- Term substitution preserves typing up to subtyping
  (TOPLAS Lemma A.1.2; AFP `A-1-2`), in agreement form: every variable the
  source context binds is replaced by a term typed at a subtype. -/
  theorem Typing.subst {ct : ClassTable} (hwf : WellFormed ct) {Γ Δ : Ctx}
      {s : List (VName × Expr)} {e : Expr} {D : CName}
      (hagr : ∀ x B, Δ x = some B →
        ∃ A, Typing ct Γ (substMany s (.var x)) A ∧ Subtype ct A B)
      (h : Typing ct Δ e D) :
      ∃ C, Typing ct Γ (substMany s e) C ∧ Subtype ct C D :=
    match h with
    | .var hx => hagr _ _ hx
    | .field he hf hm => by
      obtain ⟨C0, hC0, hsub⟩ := Typing.subst hwf hagr he
      obtain ⟨gs, hgs⟩ := fields_of_subtype hwf hsub hf
      exact ⟨_, .field hC0 hgs (List.mem_append_left _ hm), Relation.ReflTransGen.refl⟩
    | .invk he hm ha => by
      obtain ⟨C0, hC0, hsub⟩ := Typing.subst hwf hagr he
      exact ⟨_, .invk hC0 (mtype_of_subtype hwf hsub hm) (ArgsTyping.subst hwf hagr ha),
        Relation.ReflTransGen.refl⟩
    | .new hf ha => ⟨_, .new hf (ArgsTyping.subst hwf hagr ha), Relation.ReflTransGen.refl⟩
    | .ucast he hs => by
      obtain ⟨C0, hC0, hsub⟩ := Typing.subst hwf hagr he
      exact ⟨_, .ucast hC0 (Relation.ReflTransGen.trans hsub hs), Relation.ReflTransGen.refl⟩
    | @Typing.dcast _ _ _ _ C he _ _ => by
      obtain ⟨C0, hC0, hsub⟩ := Typing.subst hwf hagr he
      refine ⟨C, ?_, Relation.ReflTransGen.refl⟩
      by_cases hup : Subtype ct C0 C
      · exact .ucast hC0 hup
      · by_cases hdown : Subtype ct C C0
        · exact .dcast hC0 hdown (fun hc => hup (hc ▸ Relation.ReflTransGen.refl))
        · exact .scast hC0 hdown hup
    | @Typing.scast _ _ _ _ C he h1 _ => by
      obtain ⟨C0, hC0, hsub⟩ := Typing.subst hwf hagr he
      refine ⟨C, ?_, Relation.ReflTransGen.refl⟩
      by_cases hup : Subtype ct C0 C
      · exact .ucast hC0 hup
      · exact .scast hC0 (fun hc => h1 (Relation.ReflTransGen.trans hc hsub)) hup

  /-- Substitution for argument typing keeps the expected type list
  (TOPLAS Lemma A.1.2; AFP `A-1-2`). -/
  theorem ArgsTyping.subst {ct : ClassTable} (hwf : WellFormed ct) {Γ Δ : Ctx}
      {s : List (VName × Expr)} {args : Expr.Args} {Bs : List CName}
      (hagr : ∀ x B, Δ x = some B →
        ∃ A, Typing ct Γ (substMany s (.var x)) A ∧ Subtype ct A B)
      (h : ArgsTyping ct Δ args Bs) :
      ArgsTyping ct Γ (substArgs s args) Bs :=
    match h with
    | .nil => .nil
    | .cons he hs ha => by
      obtain ⟨C0, hC0, hsub⟩ := Typing.subst hwf hagr he
      exact .cons hC0 (Relation.ReflTransGen.trans hsub hs) (ArgsTyping.subst hwf hagr ha)
end

/-- Every class on the superclass chain of `C` is a supertype of `C`
(helper for method-body typing). -/
private theorem subtype_of_mem_supersAux {ct : ClassTable} :
    ∀ (n : Nat) (C D : CName), D ∈ supersAux ct n C → Subtype ct C D := by
  intro n
  induction n with
  | zero =>
    intro C D h
    simp only [supersAux, List.not_mem_nil] at h
  | succ n ih =>
    intro C D h
    by_cases hC : C = Object
    · have e : supersAux ct (n + 1) C = [Object] := by
        simp only [supersAux]
        rw [ite_eq_left hC]
      rw [e, List.mem_singleton] at h
      rw [h, ← hC]
      exact Relation.ReflTransGen.refl
    · cases hlk : lookupClass ct C with
      | none =>
        have e : supersAux ct (n + 1) C = [C] := by
          simp only [supersAux]
          rw [ite_eq_right hC, hlk]
        rw [e, List.mem_singleton] at h
        rw [h]
        exact Relation.ReflTransGen.refl
      | some cd =>
        have e : supersAux ct (n + 1) C = C :: supersAux ct n cd.super := by
          simp only [supersAux]
          rw [ite_eq_right hC, hlk]
        rw [e, List.mem_cons] at h
        rcases h with h | h
        · rw [h]
          exact Relation.ReflTransGen.refl
        · have hedge : directExtends ct C cd.super :=
            ⟨cd, List.mem_of_find?_eq_some hlk,
              beq_iff_eq.mp (List.find?_some (p := fun d : ClassDecl => d.name == C) hlk),
              rfl⟩
          exact Relation.ReflTransGen.head hedge (ih cd.super D h)

/-- A method lookup hit comes from a class on the superclass chain that
declares the method (helper for method-body typing). -/
private theorem lookupMethod_origin {ct : ClassTable} {m : MName} {C : CName}
    {md : MethodDecl} (h : lookupMethod ct m C = some md) :
    ∃ D0 cd, D0 ∈ supers ct C ∧ lookupClass ct D0 = some cd ∧ (m, md) ∈ cd.methods := by
  obtain ⟨D0, hD0, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · cases hf
  · obtain ⟨cd, hcd, hm⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp hm
    have hpm : p.1 = m :=
      beq_iff_eq.mp (List.find?_some (p := fun q : MName × MethodDecl => q.1 == m) hp)
    refine ⟨D0, cd, hD0, hcd, ?_⟩
    rw [← hpm, ← hpe]
    exact List.mem_of_find?_eq_some hp

/-- The body a method lookup finds types in its declaring class's method
context at a subtype of the declared return type
(TOPLAS Lemma A.1.4; AFP `A-1-4`). -/
theorem method_body_typing {ct : ClassTable} (hok : TableOk ct) {m : MName}
    {C0 : CName} {Ds : List CName} {D : CName} {xs : List VName} {e : Expr}
    (hmt : mtype ct m C0 = some (Ds, D)) (hmb : mbody ct m C0 = some (xs, e)) :
    ∃ D0, Subtype ct C0 D0 ∧ ∃ C, Subtype ct C D ∧
      Typing ct (contextOf D0 (Ds.zip xs)) e C := by
  obtain ⟨md, hmd, heq1⟩ := Option.map_eq_some_iff.mp hmt
  obtain ⟨md', hmd', heq2⟩ := Option.map_eq_some_iff.mp hmb
  rw [hmd, Option.some.injEq] at hmd'
  subst hmd'
  simp only [Prod.mk.injEq] at heq1 heq2
  obtain ⟨D0, cd, hD0, hlk, hmem⟩ := lookupMethod_origin hmd
  have hcd : cd ∈ ct := List.mem_of_find?_eq_some hlk
  have hname : cd.name = D0 :=
    beq_iff_eq.mp (List.find?_some (p := fun d : ClassDecl => d.name == D0) hlk)
  obtain ⟨A, hA, hAsub⟩ := ((hok cd hcd).2 (m, md) hmem).1
  have hzip : Ds.zip xs = md.params := (List.zip_of_prod heq1.1 heq2.1).symm
  refine ⟨D0, subtype_of_mem_supersAux _ _ _ hD0, A, ?_, ?_⟩
  · rw [← heq1.2]
    exact hAsub
  · rw [hzip, ← hname, ← heq2.2]
    exact hA

/-- A variable substitution hit returns the paired term
(helper for the method-invocation substitution). -/
private theorem substMany_var_of_find {s : List (VName × Expr)} {x a : VName} {u : Expr}
    (h : s.find? (fun p => p.1 == x) = some (a, u)) :
    substMany s (.var x) = u := by
  simp only [substMany, h]

/-- A parameter bound in the zipped method context is substituted by the
argument at the same position, typed at a subtype of the parameter type
(helper for the method-invocation substitution). -/
private theorem zipArgs_find_typed {ct : ClassTable} {Γ : Ctx} :
    ∀ (xs : List VName) (Bs : List CName) (us : Expr.Args),
      ArgsTyping ct Γ us Bs → xs.length = Bs.length →
      ∀ (x : VName) (B : CName),
        ((Bs.zip xs).find? (fun p => p.2 == x)).map Prod.fst = some B →
        ∃ a u A, (zipArgs xs us).find? (fun p => p.1 == x) = some (a, u) ∧
          Typing ct Γ u A ∧ Subtype ct A B := by
  intro xs
  induction xs with
  | nil =>
    intro Bs us _ _ x B h
    simp only [List.zip_nil_right, List.find?_nil, Option.map_none, reduceCtorEq] at h
  | cons y ys ih =>
    intro Bs us hus hlen x B h
    cases hus with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.add_one_ne_zero] at hlen
    | @cons u us' A B0 Bs' hu hsub hrest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hz : zipArgs (y :: ys) (.cons u us') = (y, u) :: zipArgs ys us' := rfl
      rw [hz]
      by_cases hy : y = x
      · subst hy
        rw [List.zip_cons_cons, List.find?_cons_of_pos (p := fun p : CName × VName => p.2 == y)
          (beq_self_eq_true _), Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨y, u, A, List.find?_cons_of_pos (p := fun p : VName × Expr => p.1 == y)
          (beq_self_eq_true _), hu, hsub⟩
      · have hne : ¬ (y == x) = true := by
          rw [beq_iff_eq]
          exact hy
        rw [List.zip_cons_cons, List.find?_cons_of_neg (p := fun p : CName × VName => p.2 == x)
          hne] at h
        obtain ⟨a, u', A', hf, hu', hs'⟩ := ih Bs' us' hrest hlen x B h
        rw [List.find?_cons_of_neg (p := fun p : VName × Expr => p.1 == x) hne]
        exact ⟨a, u', A', hf, hu', hs'⟩

/-- Substituting the receiver and arguments into a method body, the exact
instance the invocation step produces (TOPLAS Thm 2.4.1 proof, R-INVK case,
composing Lemmas A.1.4 and A.1.2). -/
theorem Typing.subst_method_body {ct : ClassTable} (hwf : WellFormed ct)
    {Γ : Ctx} {D0 B C0 : CName} {Bs : List CName} {xs : List VName}
    {e d : Expr} {us : Expr.Args} (hlen : xs.length = Bs.length)
    (hbody : Typing ct (contextOf D0 (Bs.zip xs)) e B)
    (hd : Typing ct Γ d C0) (hsub : Subtype ct C0 D0)
    (hus : ArgsTyping ct Γ us Bs) :
    ∃ C, Typing ct Γ (substMany ((thisVar, d) :: zipArgs xs us) e) C ∧
      Subtype ct C B := by
  refine Typing.subst hwf (fun x A hx => ?_) hbody
  by_cases hxt : x = thisVar
  · subst hxt
    simp only [contextOf, ↓reduceIte, Option.some.injEq] at hx
    subst hx
    refine ⟨C0, ?_, hsub⟩
    rw [substMany_var_of_find (a := thisVar)
      (List.find?_cons_of_pos (p := fun p : VName × Expr => p.1 == thisVar)
        (beq_self_eq_true _))]
    exact hd
  · simp only [contextOf, hxt, ↓reduceIte] at hx
    obtain ⟨a, u, A', hf, hu, hs⟩ := zipArgs_find_typed xs Bs us hus hlen x A hx
    have hne : ¬ (thisVar == x) = true := by
      rw [beq_iff_eq]
      exact fun h => hxt h.symm
    refine ⟨A', ?_, hs⟩
    rw [substMany_var_of_find (a := a)
      (by rw [List.find?_cons_of_neg (p := fun p : VName × Expr => p.1 == x) hne]; exact hf)]
    exact hu

end Cslib.FeatherweightJava
