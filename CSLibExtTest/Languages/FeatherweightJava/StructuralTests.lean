/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.FeatherweightJava.Structural
public import CSLibExtTest.Languages.FeatherweightJava.BasicTests

/-!
Tests for the Featherweight Java structural lemmas, on the Pair fixtures
of the core test module.
-/

@[expose] public section
set_option autoImplicit false
namespace Cslib.FeatherweightJava
namespace Tests

/-- Acceptance instance: the `setfst` body with `this` replaced by a Pair
of A's and its parameter by a B, exactly as the invocation step substitutes,
types at a subtype of Pair in the empty context. -/
theorem setfst_subst_typing :
    ∃ C, Typing pairTable (fun _ => none)
      (substMany
        ((thisVar,
          Expr.new classPair
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                Expr.Args.nil))) ::
          zipArgs [newfstV]
            (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil))
        (Expr.new classPair
          (Expr.Args.cons (Expr.var newfstV)
            (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
              Expr.Args.nil))))
      C ∧ Subtype pairTable C classPair := by
  have hAO : Subtype pairTable classA Object :=
    Relation.ReflTransGen.single (by unfold directExtends; decide)
  have hBO : Subtype pairTable classB Object :=
    Relation.ReflTransGen.head (b := classA) (by unfold directExtends; decide) hAO
  have hfP : fields pairTable classPair = some [(Object, fstF), (Object, sndF)] := by decide
  have hA : Typing pairTable (fun _ => none) (Expr.new classA Expr.Args.nil) classA :=
    Typing.new (fs := []) (by decide) ArgsTyping.nil
  refine ⟨classPair, ?_, Relation.ReflTransGen.refl⟩
  exact Typing.new hfP
    (ArgsTyping.cons (Typing.new (fs := []) (by decide) ArgsTyping.nil) hBO
      (ArgsTyping.cons
        (Typing.field (Typing.new hfP (ArgsTyping.cons hA hAO (ArgsTyping.cons hA hAO
          ArgsTyping.nil))) hfP (by decide))
        Relation.ReflTransGen.refl ArgsTyping.nil))

/-- Concrete check of the same instance: the substituted body is a Pair of
a B and the second component of the receiver, and it types at Pair. -/
theorem setfst_substituted_typing :
    Typing pairTable (fun _ => none)
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons
            (Expr.fld
              (Expr.new classPair
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                    Expr.Args.nil)))
              sndF)
            Expr.Args.nil)))
      classPair := by
  have hAO : Subtype pairTable classA Object :=
    Relation.ReflTransGen.single (by unfold directExtends; decide)
  have hBO : Subtype pairTable classB Object :=
    Relation.ReflTransGen.head (b := classA) (by unfold directExtends; decide) hAO
  have hfP : fields pairTable classPair = some [(Object, fstF), (Object, sndF)] := by decide
  have hA : Typing pairTable (fun _ => none) (Expr.new classA Expr.Args.nil) classA :=
    Typing.new (fs := []) (by decide) ArgsTyping.nil
  exact Typing.new hfP
    (ArgsTyping.cons (Typing.new (fs := []) (by decide) ArgsTyping.nil) hBO
      (ArgsTyping.cons
        (Typing.field (Typing.new hfP (ArgsTyping.cons hA hAO (ArgsTyping.cons hA hAO
          ArgsTyping.nil))) hfP (by decide))
        Relation.ReflTransGen.refl ArgsTyping.nil))

/-- The overriding `setfst` in SubPair keeps the Pair method type
(instance of `mtype_of_subtype`). -/
theorem mtype_setfst_subPair :
    mtype subPairTable setfstM classSubPair = some ([Object], classPair) := by
  decide

/-- The `setfst` body types in its declaring class's method context
(instance of `method_body_typing`). -/
theorem setfst_body_typing :
    ∃ C, Subtype pairTable C classPair ∧
      Typing pairTable (contextOf classPair [(Object, newfstV)])
        (Expr.new classPair
          (Expr.Args.cons (Expr.var newfstV)
            (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
              Expr.Args.nil)))
        C := by
  have hfP : fields pairTable classPair = some [(Object, fstF), (Object, sndF)] := by decide
  exact ⟨classPair, Relation.ReflTransGen.refl,
    Typing.new hfP
      (ArgsTyping.cons (Typing.var (by decide)) Relation.ReflTransGen.refl
        (ArgsTyping.cons (Typing.field (Typing.var (by decide)) hfP (by decide))
          Relation.ReflTransGen.refl ArgsTyping.nil))⟩

end Tests
end Cslib.FeatherweightJava
