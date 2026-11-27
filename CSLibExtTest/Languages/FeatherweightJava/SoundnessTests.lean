/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.FeatherweightJava.Soundness
public import CSLibExtTest.Languages.FeatherweightJava.BasicTests

/-!
Tests for Featherweight Java subject reduction, progress and type soundness under the
call-by-value `Step`, on the Pair fixtures of the core test module.

Statement pins restate every public declaration of the module, constructors of `CastStuck`
included, and are closed by the declaration itself, so a weakened or drifted statement fails
here. Concrete checks: the failed downcast `(B) (new A())` is typed, cast-stuck, not a value
and normal, and progress lands in its cast-failure disjunct; the stupid-cast step of TOPLAS
p. 405 (`(Pair) (Object) (new A())` to `(Pair) (new A())`, typable only by T-SCast); an upcast
whose result has no typing at the original type; dynamic dispatch to an overriding body typed
strictly below the declared return type; two soundness runs, one ending stuck and one at a
value; every congruence constructor of `CastStuck`; and negative controls showing that the
empty context, the typing hypotheses and `TableOk` cannot be dropped and that `CastStuck` is
not trivially true.
-/

@[expose] public section
set_option autoImplicit false
namespace Cslib.FeatherweightJava
namespace Tests

/-! ### Statement pins -/

/-- Pin: the failed-cast constructor of `CastStuck`. -/
theorem castStuck_cast_pin : ∀ {ct : ClassTable} {C D : CName} {vs : Expr.Args},
    ArgsValue vs → ¬ Subtype ct C D → CastStuck ct (.cast D (.new C vs)) :=
  @CastStuck.cast

/-- Pin: field-receiver congruence of `CastStuck`. -/
theorem castStuck_fldCongr_pin : ∀ {ct : ClassTable} {e : Expr} {f : FName},
    CastStuck ct e → CastStuck ct (.fld e f) :=
  @CastStuck.fldCongr

/-- Pin: invocation-receiver congruence of `CastStuck`. -/
theorem castStuck_invkRecv_pin : ∀ {ct : ClassTable} {e : Expr} {m : MName} {args : Expr.Args},
    CastStuck ct e → CastStuck ct (.invk e m args) :=
  @CastStuck.invkRecv

/-- Pin: invocation-argument congruence of `CastStuck`, behind a value receiver. -/
theorem castStuck_invkArgs_pin : ∀ {ct : ClassTable} {C : CName} {vs args : Expr.Args}
    {m : MName}, ArgsValue vs → ArgsCastStuck ct args → CastStuck ct (.invk (.new C vs) m args) :=
  @CastStuck.invkArgs

/-- Pin: constructor-argument congruence of `CastStuck`. -/
theorem castStuck_newArgs_pin : ∀ {ct : ClassTable} {C : CName} {args : Expr.Args},
    ArgsCastStuck ct args → CastStuck ct (.new C args) :=
  @CastStuck.newArgs

/-- Pin: cast-subject congruence of `CastStuck`. -/
theorem castStuck_castCongr_pin : ∀ {ct : ClassTable} {C : CName} {e : Expr},
    CastStuck ct e → CastStuck ct (.cast C e) :=
  @CastStuck.castCongr

/-- Pin: an argument list is stuck at its head. -/
theorem argsCastStuck_head_pin : ∀ {ct : ClassTable} {e : Expr} {args : Expr.Args},
    CastStuck ct e → ArgsCastStuck ct (.cons e args) :=
  @ArgsCastStuck.head

/-- Pin: an argument list is stuck in its tail, behind a value. -/
theorem argsCastStuck_tail_pin : ∀ {ct : ClassTable} {v : Expr} {args : Expr.Args},
    Value v → ArgsCastStuck ct args → ArgsCastStuck ct (.cons v args) :=
  @ArgsCastStuck.tail

/-- Pin: values do not step. -/
theorem value_not_step_pin : ∀ {ct : ClassTable} {e e' : Expr}, Value e → ¬ Step ct e e' :=
  @Value.not_step

/-- Pin: value argument lists do not step. -/
theorem argsValue_not_argsStep_pin : ∀ {ct : ClassTable} {args args' : Expr.Args},
    ArgsValue args → ¬ ArgsStep ct args args' :=
  @ArgsValue.not_argsStep

/-- Pin: a cast-stuck expression is not a value. -/
theorem castStuck_not_value_pin : ∀ {ct : ClassTable} {e : Expr}, CastStuck ct e → ¬ Value e :=
  @CastStuck.not_value

/-- Pin: a cast-stuck argument list is not a value list. -/
theorem argsCastStuck_not_argsValue_pin : ∀ {ct : ClassTable} {args : Expr.Args},
    ArgsCastStuck ct args → ¬ ArgsValue args :=
  @ArgsCastStuck.not_argsValue

/-- Pin: a cast-stuck expression does not step. -/
theorem castStuck_not_step_pin : ∀ {ct : ClassTable} {e e' : Expr},
    CastStuck ct e → ¬ Step ct e e' :=
  @CastStuck.not_step

/-- Pin: a cast-stuck argument list does not step. -/
theorem argsCastStuck_not_argsStep_pin : ∀ {ct : ClassTable} {args args' : Expr.Args},
    ArgsCastStuck ct args → ¬ ArgsStep ct args args' :=
  @ArgsCastStuck.not_argsStep

/-- Pin: argument typing preserves length. -/
theorem argsTyping_length_eq_pin : ∀ {ct : ClassTable} {Γ : Ctx} {args : Expr.Args}
    {Bs : List CName}, ArgsTyping ct Γ args Bs → args.length = Bs.length :=
  @ArgsTyping.length_eq

/-- Pin: inversion of T-New. -/
theorem typing_new_inv_pin : ∀ {ct : ClassTable} {Γ : Ctx} {C D : CName} {args : Expr.Args},
    Typing ct Γ (.new C args) D →
      D = C ∧ ∃ fs, fields ct C = some fs ∧ ArgsTyping ct Γ args (fs.map Prod.fst) :=
  @Typing.new_inv

/-- Pin: inversion of T-Field. -/
theorem typing_fld_inv_pin : ∀ {ct : ClassTable} {Γ : Ctx} {e : Expr} {f : FName} {Ci : CName},
    Typing ct Γ (.fld e f) Ci → ∃ C fs, Typing ct Γ e C ∧ fields ct C = some fs ∧ (Ci, f) ∈ fs :=
  @Typing.fld_inv

/-- Pin: inversion of T-Invk. -/
theorem typing_invk_inv_pin : ∀ {ct : ClassTable} {Γ : Ctx} {e : Expr} {m : MName}
    {args : Expr.Args} {B0 : CName}, Typing ct Γ (.invk e m args) B0 →
      ∃ C Bs, Typing ct Γ e C ∧ mtype ct m C = some (Bs, B0) ∧ ArgsTyping ct Γ args Bs :=
  @Typing.invk_inv

/-- Pin: inversion of the cast rules. -/
theorem typing_cast_inv_pin : ∀ {ct : ClassTable} {Γ : Ctx} {C D : CName} {e : Expr},
    Typing ct Γ (.cast C e) D → D = C ∧ ∃ D', Typing ct Γ e D' :=
  @Typing.cast_inv

/-- Pin: typing of the selected field value. -/
theorem fieldValue_typing_pin : ∀ {ct : ClassTable} {Γ : Ctx} {fs : List (CName × FName)}
    {args : Expr.Args} {Ci : CName} {f : FName} {v : Expr}, (fs.map Prod.snd).Nodup →
      (Ci, f) ∈ fs → ArgsTyping ct Γ args (fs.map Prod.fst) → fieldValue fs args f = some v →
        ∃ A, Typing ct Γ v A ∧ Subtype ct A Ci :=
  @fieldValue_typing

/-- Pin: existence of the selected field value. -/
theorem exists_fieldValue_pin : ∀ {fs : List (CName × FName)} {args : Expr.Args} {Ci : CName}
    {f : FName}, (Ci, f) ∈ fs → args.length = fs.length → ∃ v, fieldValue fs args f = some v :=
  @exists_fieldValue

/-- Pin: any cast of a typed expression is typed. -/
theorem typing_recast_pin : ∀ {ct : ClassTable} {Γ : Ctx} {e : Expr} {C C' : CName},
    Typing ct Γ e C' → Typing ct Γ (.cast C e) C :=
  @Typing.recast

/-- Pin: TOPLAS Theorem 2.4.2 (1), with no class-table hypothesis. -/
theorem typing_fields_of_fld_new_pin : ∀ {ct : ClassTable} {Γ : Ctx} {C0 : CName}
    {es : Expr.Args} {f : FName} {C : CName}, Typing ct Γ (.fld (.new C0 es) f) C →
      ∃ fs, fields ct C0 = some fs ∧ ∃ Ci, (Ci, f) ∈ fs :=
  @Typing.fields_of_fld_new

/-- Pin: TOPLAS Theorem 2.4.2 (2), with no class-table hypothesis. -/
theorem typing_mbody_of_invk_new_pin : ∀ {ct : ClassTable} {Γ : Ctx} {C0 : CName}
    {es : Expr.Args} {m : MName} {ds : Expr.Args} {C : CName},
    Typing ct Γ (.invk (.new C0 es) m ds) C →
      ∃ xs e0, mbody ct m C0 = some (xs, e0) ∧ xs.length = ds.length :=
  @Typing.mbody_of_invk_new

/-- Pin: subject reduction (TOPLAS Theorem 2.4.1 for the call-by-value `Step`). -/
theorem typing_subject_reduction_pin : ∀ {ct : ClassTable}, ValidTable ct → ∀ {Γ : Ctx}
    {e e' : Expr} {C : CName}, Typing ct Γ e C → Step ct e e' →
      ∃ C', Typing ct Γ e' C' ∧ Subtype ct C' C :=
  @Typing.subject_reduction

/-- Pin: subject reduction for argument lists. -/
theorem argsTyping_subject_reduction_pin : ∀ {ct : ClassTable}, ValidTable ct → ∀ {Γ : Ctx}
    {args args' : Expr.Args} {Bs : List CName}, ArgsTyping ct Γ args Bs →
      ArgsStep ct args args' → ArgsTyping ct Γ args' Bs :=
  @ArgsTyping.subject_reduction

/-- Pin: multi-step subject reduction. -/
theorem typing_subject_reduction_steps_pin : ∀ {ct : ClassTable}, ValidTable ct → ∀ {Γ : Ctx}
    {e e' : Expr} {C : CName}, Typing ct Γ e C → Steps ct e e' →
      ∃ C', Typing ct Γ e' C' ∧ Subtype ct C' C :=
  @Typing.subject_reduction_steps

/-- Pin: progress modulo failed casts, with no class-table hypothesis. -/
theorem typing_progress_pin : ∀ {ct : ClassTable} {e : Expr} {C : CName},
    Typing ct (fun _ => none) e C → Value e ∨ CastStuck ct e ∨ ∃ e', Step ct e e' :=
  @Typing.progress

/-- Pin: progress for argument lists. -/
theorem argsTyping_progress_pin : ∀ {ct : ClassTable} {args : Expr.Args} {Bs : List CName},
    ArgsTyping ct (fun _ => none) args Bs →
      ArgsValue args ∨ ArgsCastStuck ct args ∨ ∃ args', ArgsStep ct args args' :=
  @ArgsTyping.progress

/-- Pin: type soundness (TOPLAS Theorem 2.4.3 for the call-by-value `Step`). -/
theorem typing_soundness_pin : ∀ {ct : ClassTable}, ValidTable ct → ∀ {e e' : Expr} {C : CName},
    Typing ct (fun _ => none) e C → Steps ct e e' → Relation.Normal (Step ct) e' →
      (Value e' ∧ ∃ D, Typing ct (fun _ => none) e' D ∧ Subtype ct D C) ∨ CastStuck ct e' :=
  @Typing.soundness

/-! ### Fixtures -/

/-- `new A()`. -/
abbrev newA : Expr := .new classA .nil

/-- `new B()`. -/
abbrev newB : Expr := .new classB .nil

/-- `new Pair(new A(), new A())`. -/
abbrev pairAA : Expr := .new classPair (.cons newA (.cons newA .nil))

/-- The failed downcast `(B) (new A())`. -/
abbrev badCast : Expr := .cast classB newA

/-- Upward closure (test helper): a list of class names that contains `C` and is closed under
the superclass edges of `ct` contains every supertype of `C`. -/
theorem mem_of_subtype_of_closed {ct : ClassTable} {S : List CName} {C D : CName}
    (hC : C ∈ S) (hS : ∀ cd ∈ ct, cd.name ∈ S → cd.super ∈ S) (h : Subtype ct C D) : D ∈ S := by
  induction h with
  | refl => exact hC
  | tail _ hd ih =>
    obtain ⟨cd, hmem, rfl, rfl⟩ := hd
    exact hS cd hmem ih

/-- A is a subtype of Object. -/
theorem subtype_A_Object : Subtype pairTable classA Object :=
  Relation.ReflTransGen.single (by unfold directExtends; decide)

/-- Pair is a subtype of Object. -/
theorem subtype_Pair_Object : Subtype pairTable classPair Object :=
  Relation.ReflTransGen.single (by unfold directExtends; decide)

/-- A is not a subtype of Pair. -/
theorem not_subtype_A_Pair : ¬ Subtype pairTable classA classPair := fun h =>
  absurd (mem_of_subtype_of_closed (S := [classA, Object]) (by decide) (by decide) h) (by decide)

/-- Pair is not a subtype of A. -/
theorem not_subtype_Pair_A : ¬ Subtype pairTable classPair classA := fun h =>
  absurd (mem_of_subtype_of_closed (S := [classPair, Object]) (by decide) (by decide) h)
    (by decide)

/-- `new A()` types at A in every context. -/
theorem typing_newA {Γ : Ctx} : Typing pairTable Γ newA classA :=
  Typing.new (fs := []) (by decide) ArgsTyping.nil

/-- `new B()` types at B in every context. -/
theorem typing_newB {Γ : Ctx} : Typing pairTable Γ newB classB :=
  Typing.new (fs := []) (by decide) ArgsTyping.nil

/-- `new Pair(new A(), new A())` types at Pair in every context. -/
theorem typing_pairAA {Γ : Ctx} : Typing pairTable Γ pairAA classPair :=
  Typing.new fields_pair (ArgsTyping.cons typing_newA subtype_A_Object
    (ArgsTyping.cons typing_newA subtype_A_Object ArgsTyping.nil))

/-! ### Acceptance: the failed downcast is stuck and typed -/

/-- `(B) (new A())` types at B by T-DCast. -/
theorem badCast_typing : Typing pairTable (fun _ => none) badCast classB :=
  Typing.dcast typing_newA subtype_B_A (by decide)

/-- `(B) (new A())` is stuck at a failed downcast. -/
theorem badCast_castStuck : CastStuck pairTable badCast :=
  CastStuck.cast ArgsValue.nil not_subtype_A_B

/-- `(B) (new A())` is not a value. -/
theorem badCast_not_value : ¬ Value badCast := fun h => nomatch h

/-- `(B) (new A())` has no step (the core test `cast_bad_stuck`). -/
theorem badCast_normal : Relation.Normal (Step pairTable) badCast := cast_bad_stuck

/-- Progress lands in its cast-failure disjunct on `(B) (new A())`. -/
theorem badCast_progress : CastStuck pairTable badCast := by
  rcases Typing.progress badCast_typing with hv | hc | hs
  · exact absurd hv badCast_not_value
  · exact hc
  · exact absurd hs badCast_normal

/-- The module's lemmas agree with the direct checks: not a value, no step. -/
theorem badCast_not_value_not_step :
    ¬ Value badCast ∧ ∀ e', ¬ Step pairTable badCast e' :=
  ⟨badCast_castStuck.not_value, fun _ => badCast_castStuck.not_step⟩

/-! ### The stupid cast is needed (TOPLAS p. 405) -/

/-- `(Pair) (Object) (new A())`. -/
abbrev stupidSrc : Expr := .cast classPair (.cast Object newA)

/-- `(Pair) (new A())`. -/
abbrev stupidTgt : Expr := .cast classPair newA

/-- `(Pair) (Object) (new A())` types at Pair by T-DCast over T-UCast. -/
theorem stupidSrc_typing : Typing pairTable (fun _ => none) stupidSrc classPair :=
  Typing.dcast (Typing.ucast typing_newA subtype_A_Object) subtype_Pair_Object (by decide)

/-- The inner upcast steps: `(Pair) (Object) (new A())` to `(Pair) (new A())`. -/
theorem stupid_step : Step pairTable stupidSrc stupidTgt :=
  Step.castCongr (Step.cast ArgsValue.nil subtype_A_Object)

/-- `(Pair) (new A())` types at Pair by T-SCast. -/
theorem stupidTgt_typing : Typing pairTable (fun _ => none) stupidTgt classPair :=
  Typing.scast typing_newA not_subtype_Pair_A not_subtype_A_Pair

/-- Every typing of `(Pair) (new A())` is by T-SCast: neither T-UCast nor T-DCast applies. -/
theorem stupidTgt_typing_is_scast {Γ : Ctx} {C : CName} (h : Typing pairTable Γ stupidTgt C) :
    ∃ D, Typing pairTable Γ newA D ∧ ¬ Subtype pairTable C D ∧ ¬ Subtype pairTable D C := by
  cases h with
  | ucast he hs =>
    cases he
    exact absurd hs not_subtype_A_Pair
  | dcast he hs _ =>
    cases he
    exact absurd hs not_subtype_Pair_A
  | scast he h1 h2 => exact ⟨_, he, h1, h2⟩

/-- Subject reduction on the stupid-cast step. -/
theorem stupid_subject_reduction :
    ∃ C', Typing pairTable (fun _ => none) stupidTgt C' ∧ Subtype pairTable C' classPair :=
  Typing.subject_reduction pairTable_valid stupidSrc_typing stupid_step

/-- `(Pair) (new A())` is stuck at a failed cast. -/
theorem stupidTgt_castStuck : CastStuck pairTable stupidTgt :=
  CastStuck.cast ArgsValue.nil not_subtype_A_Pair

/-! ### Subtyping in subject reduction is necessary -/

/-- `(A) (new B())` types at A by T-UCast. -/
theorem upCast_typing : Typing pairTable (fun _ => none) (.cast classA newB) classA :=
  Typing.ucast typing_newB subtype_B_A

/-- `new B()`, the result of the upcast step `cast_up_step`, has no typing at A. -/
theorem newB_not_typing_A {Γ : Ctx} : ¬ Typing pairTable Γ newB classA := by
  intro h
  generalize hC : classA = C at h
  cases h
  exact absurd hC (by decide)

/-- Subject reduction on the upcast step gives a strict subtype. -/
theorem upCast_subject_reduction :
    ∃ C', Typing pairTable (fun _ => none) newB C' ∧ Subtype pairTable C' classA :=
  Typing.subject_reduction pairTable_valid upCast_typing cast_up_step

/-! ### Dynamic dispatch -/

/-- `new SubPair(new A(), new A())`. -/
abbrev subPairAA : Expr := .new classSubPair (.cons newA (.cons newA .nil))

/-- `new SubPair(new A(), new A()).setfst(new B())`. -/
abbrev dispatchSrc : Expr := .invk subPairAA setfstM (.cons newB .nil)

/-- The overriding body after substitution. -/
abbrev dispatchTgt : Expr :=
  .new classSubPair (.cons newB (.cons (.fld subPairAA sndF) .nil))

/-- SubPair is a subtype of Pair. -/
theorem subtype_SubPair_Pair : Subtype subPairTable classSubPair classPair :=
  Relation.ReflTransGen.single (by unfold directExtends; decide)

/-- The invocation dispatches to the overriding `setfst` of SubPair. -/
theorem dispatch_step : Step subPairTable dispatchSrc dispatchTgt :=
  Step.invk (ArgsValue.cons (Value.new _ _ ArgsValue.nil)
      (ArgsValue.cons (Value.new _ _ ArgsValue.nil) ArgsValue.nil))
    (ArgsValue.cons (Value.new _ _ ArgsValue.nil) ArgsValue.nil) subpair_mbody_override rfl

/-- The invocation types at Pair, the declared return type. -/
theorem dispatchSrc_typing : Typing subPairTable (fun _ => none) dispatchSrc classPair := by
  have hAO : Subtype subPairTable classA Object :=
    Relation.ReflTransGen.single (by unfold directExtends; decide)
  have hBO : Subtype subPairTable classB Object :=
    Relation.ReflTransGen.head (b := classA) (by unfold directExtends; decide) hAO
  have hA : Typing subPairTable (fun _ => none) newA classA :=
    Typing.new (fs := []) (by decide) ArgsTyping.nil
  exact Typing.invk
    (Typing.new (fs := [(Object, fstF), (Object, sndF)]) (by decide)
      (ArgsTyping.cons hA hAO (ArgsTyping.cons hA hAO ArgsTyping.nil)))
    (by decide : mtype subPairTable setfstM classSubPair = some ([Object], classPair))
    (ArgsTyping.cons (Typing.new (fs := []) (by decide) ArgsTyping.nil) hBO ArgsTyping.nil)

/-- The result types at SubPair, strictly below Pair, and at no other class. -/
theorem dispatchTgt_types_only_at_SubPair {Γ : Ctx} {C : CName}
    (h : Typing subPairTable Γ dispatchTgt C) : C = classSubPair ∧ classSubPair ≠ classPair := by
  cases h
  exact ⟨rfl, by decide⟩

/-- Subject reduction on the dispatch step. -/
theorem dispatch_subject_reduction :
    ∃ C', Typing subPairTable (fun _ => none) dispatchTgt C' ∧ Subtype subPairTable C' classPair :=
  Typing.subject_reduction subPairTable_valid dispatchSrc_typing dispatch_step

/-! ### Soundness runs -/

/-- `(B) (new Pair(new A(), new A()).fst)` types at B. -/
theorem castFst_typing :
    Typing pairTable (fun _ => none) (.cast classB (.fld pairAA fstF)) classB :=
  Typing.dcast (Typing.field typing_pairAA fields_pair (by decide))
    (Relation.ReflTransGen.trans subtype_B_A subtype_A_Object) (by decide)

/-- It steps to the failed downcast `(B) (new A())`. -/
theorem castFst_step : Step pairTable (.cast classB (.fld pairAA fstF)) badCast :=
  Step.castCongr (Step.proj (ArgsValue.cons (Value.new _ _ ArgsValue.nil)
    (ArgsValue.cons (Value.new _ _ ArgsValue.nil) ArgsValue.nil)) fields_pair (by decide))

/-- Soundness ends the run at the failed downcast. -/
theorem castFst_soundness : CastStuck pairTable badCast := by
  rcases Typing.soundness pairTable_valid castFst_typing (Relation.ReflTransGen.single castFst_step)
      badCast_normal with ⟨hv, -⟩ | hc
  · exact absurd hv badCast_not_value
  · exact hc

/-- `new Pair(new B(), new A())`, the result of `swap`. -/
abbrev pairBA : Expr := .new classPair (.cons newB (.cons newA .nil))

/-- `new Pair(new B(), new A())` is a value. -/
theorem pairBA_value : Value pairBA :=
  Value.new _ _ (ArgsValue.cons (Value.new _ _ ArgsValue.nil)
    (ArgsValue.cons (Value.new _ _ ArgsValue.nil) ArgsValue.nil))

/-- Soundness ends the `swap` run (core tests `typing_pair_swap`, `pair_swap_eval`) at a value
typed at a subtype of Pair. -/
theorem swap_soundness :
    ∃ D, Typing pairTable (fun _ => none) pairBA D ∧ Subtype pairTable D classPair := by
  rcases Typing.soundness pairTable_valid typing_pair_swap pair_swap_eval
      (fun ⟨_, hs⟩ => pairBA_value.not_step hs) with ⟨-, hD⟩ | hc
  · exact hD
  · exact absurd pairBA_value hc.not_value

/-! ### Every congruence constructor of `CastStuck` -/

/-- A failed downcast under each evaluation context of the call-by-value `Step`. -/
theorem castStuck_congruences :
    CastStuck pairTable (.fld (.new classPair (.cons badCast (.cons newA .nil))) fstF) ∧
    CastStuck pairTable (.invk (.cast classPair badCast) swapM .nil) ∧
    CastStuck pairTable (.invk pairAA setfstM (.cons badCast .nil)) ∧
    CastStuck pairTable (.new classPair (.cons newA (.cons badCast .nil))) ∧
    CastStuck pairTable (.cast Object badCast) :=
  ⟨.fldCongr (.newArgs (.head badCast_castStuck)),
    .invkRecv (.castCongr badCast_castStuck),
    .invkArgs (ArgsValue.cons (Value.new _ _ ArgsValue.nil)
      (ArgsValue.cons (Value.new _ _ ArgsValue.nil) ArgsValue.nil)) (.head badCast_castStuck),
    .newArgs (.tail (Value.new _ _ ArgsValue.nil) (.head badCast_castStuck)),
    .castCongr badCast_castStuck⟩

/-- `new Pair(new A(), (B) (new A()))` types at Pair, and progress lands in the cast-failure
disjunct through `ArgsCastStuck.tail`. -/
theorem badInTail_progress :
    CastStuck pairTable (.new classPair (.cons newA (.cons badCast .nil))) := by
  have hBO : Subtype pairTable classB Object :=
    Relation.ReflTransGen.trans subtype_B_A subtype_A_Object
  have h : Typing pairTable (fun _ => none) (.new classPair (.cons newA (.cons badCast .nil)))
      classPair :=
    Typing.new fields_pair
      (ArgsTyping.cons typing_newA subtype_A_Object (ArgsTyping.cons badCast_typing hBO .nil))
  have hc := castStuck_congruences.2.2.2.1
  rcases Typing.progress h with hv | hc' | ⟨_, hs⟩
  · exact absurd hv hc.not_value
  · exact hc'
  · exact absurd hs hc.not_step

/-! ### Negative controls -/

/-- Progress and soundness need the empty context: a variable typed in another context is
neither a value, nor stuck at a failed cast, nor steps. -/
theorem open_var_neither :
    Typing pairTable (fun _ => some classA) (.var 1) classA ∧
    ¬ (Value (.var 1) ∨ CastStuck pairTable (.var 1) ∨ ∃ e', Step pairTable (.var 1) e') := by
  refine ⟨Typing.var rfl, ?_⟩
  rintro (h | h | ⟨_, h⟩) <;> cases h

/-- Progress needs its typing hypothesis: `new A().fst` is neither a value, nor stuck at a
failed cast, nor steps, and has no typing. -/
theorem untyped_fld_neither :
    ¬ (Value (.fld newA fstF) ∨ CastStuck pairTable (.fld newA fstF) ∨
      ∃ e', Step pairTable (.fld newA fstF) e') ∧
    ¬ ∃ C, Typing pairTable (fun _ => none) (.fld newA fstF) C := by
  have hfA : fields pairTable classA = some [] := by decide
  refine ⟨?_, ?_⟩
  · rintro (h | h | ⟨_, h⟩)
    · cases h
    · cases h with
      | fldCongr h => cases h with
        | newArgs h => cases h
    · cases h with
      | proj _ hf hv =>
        rw [hfA, Option.some.injEq] at hf
        subst hf
        cases hv
      | fldCongr h => cases h with
        | newArgs h => cases h
  · rintro ⟨C, h⟩
    cases h with
    | field he hf hm =>
      cases he
      rw [hfA, Option.some.injEq] at hf
      subst hf
      exact absurd hm List.not_mem_nil

/-- The TOPLAS Theorem 2.4.2 conclusions fail without typing: `new A().fst` names no field of
A, and `new A().swap()` finds no method body. -/
theorem redex_conclusions_fail_untyped :
    (¬ ∃ fs, fields pairTable classA = some fs ∧ ∃ Ci, (Ci, fstF) ∈ fs) ∧
    mbody pairTable swapM classA = none := by
  refine ⟨?_, by decide⟩
  rintro ⟨fs, hf, Ci, hm⟩
  rw [(by decide : fields pairTable classA = some []), Option.some.injEq] at hf
  subst hf
  exact absurd hm List.not_mem_nil

/-- `CastStuck` is not trivially true: the upcast `(A) (new B())` steps and is not stuck. -/
theorem upCast_not_castStuck :
    (∃ e', Step pairTable (.cast classA newB) e') ∧ ¬ CastStuck pairTable (.cast classA newB) := by
  refine ⟨⟨_, cast_up_step⟩, ?_⟩
  intro h
  cases h with
  | cast _ hn => exact hn subtype_B_A
  | castCongr h => cases h with
    | newArgs h => cases h

/-- A one-class table whose method `swap` on A returns `new Object()` against its declared
return type A: well-formed, but not `TableOk`. -/
def badBodyTable : ClassTable :=
  [{ name := classA, super := Object, fields := [], ctorParams := [],
     methods := [(swapM, { ret := classA, params := [], body := .new Object .nil })] }]

/-- Object is not a subtype of A in `badBodyTable`. -/
theorem badBody_not_subtype_Object_A : ¬ Subtype badBodyTable Object classA := fun h =>
  absurd (mem_of_subtype_of_closed (S := [Object]) (by decide) (by decide) h) (by decide)

/-- `badBodyTable` is well-formed. -/
theorem badBodyTable_wellFormed : WellFormed badBodyTable := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, by decide⟩
  · intro C fs h
    by_cases h0 : C = Object
    · subst h0
      rw [fields_object, Option.some.injEq] at h
      subst h
      decide
    · by_cases h1 : C = classA
      · subst h1
        rw [(by decide : fields badBodyTable classA = some []), Option.some.injEq] at h
        subst h
        decide
      · have hne : ¬ (classA == C) = true := fun hEq => h1 (beq_iff_eq.mp hEq).symm
        have hLk : lookupClass badBodyTable C = none := by
          simp only [lookupClass, badBodyTable, List.find?, hne]
        have hSup : supers badBodyTable C = [C] := by
          simp only [supers, supersAux, h0, hLk, ite_false]
        have hNone : fields badBodyTable C = none := by
          simp only [fields, h0, hSup, hLk, ite_false, List.foldl_cons, List.foldl_nil]
        cases hNone.symm.trans h
  · intro cd hcd p hp sig' hsig
    simp only [badBodyTable, List.mem_singleton] at hcd
    subst hcd
    simp only [List.mem_singleton] at hp
    subst hp
    rw [(by decide : mtype badBodyTable swapM Object = none)] at hsig
    cases hsig

/-- `badBodyTable` is not `TableOk`: the body of `swap` has no typing at a subtype of A. -/
theorem badBodyTable_not_tableOk : ¬ TableOk badBodyTable := by
  intro h
  obtain ⟨-, hm⟩ := h _ (List.mem_singleton_self _)
  obtain ⟨⟨A, hty, hsub⟩, -⟩ := hm _ (List.mem_singleton_self _)
  cases hty
  exact badBody_not_subtype_Object_A hsub

/-- Subject reduction and soundness need `TableOk`: in the well-formed `badBodyTable`,
`new A().swap()` types at A and steps to the value `new Object()`, which is normal, has no
typing at a subtype of A, and is not stuck at a failed cast. -/
theorem tableOk_needed :
    WellFormed badBodyTable ∧ ¬ TableOk badBodyTable ∧
    Typing badBodyTable (fun _ => none) (.invk newA swapM .nil) classA ∧
    Step badBodyTable (.invk newA swapM .nil) (.new Object .nil) ∧
    Relation.Normal (Step badBodyTable) (.new Object .nil) ∧
    ¬ ((Value (.new Object .nil) ∧ ∃ D, Typing badBodyTable (fun _ => none) (.new Object .nil) D ∧
        Subtype badBodyTable D classA) ∨ CastStuck badBodyTable (.new Object .nil)) := by
  refine ⟨badBodyTable_wellFormed, badBodyTable_not_tableOk, ?_, ?_, ?_, ?_⟩
  · exact Typing.invk (Typing.new (fs := []) (by decide) ArgsTyping.nil)
      (by decide : mtype badBodyTable swapM classA = some ([], classA)) ArgsTyping.nil
  · exact Step.invk ArgsValue.nil ArgsValue.nil
      (by decide : mbody badBodyTable swapM classA = some ([], .new Object .nil)) rfl
  · rintro ⟨_, hs⟩
    cases hs with
    | newArgs h => cases h
  · rintro (⟨-, D, hty, hsub⟩ | h)
    · cases hty
      exact badBody_not_subtype_Object_A hsub
    · cases h with
      | newArgs h => cases h

end Tests
end Cslib.FeatherweightJava
