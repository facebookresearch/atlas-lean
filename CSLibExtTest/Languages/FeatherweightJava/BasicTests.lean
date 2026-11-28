/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.FeatherweightJava.Basic

/-!
Tests for Featherweight Java core definitions.
-/

@[expose] public section
set_option autoImplicit false
namespace Cslib.FeatherweightJava
namespace Tests

/-- Decidable equality for expressions (test helper). -/
example : DecidableEq Expr := inferInstance

/-- Decidable equality for argument lists (test helper). -/
example : DecidableEq Expr.Args := inferInstance

/-- Test class A (extends Object). -/
def classA : CName := 1

/-- Test class B (extends A). -/
def classB : CName := 2

/-- Test class Pair (extends Object, two fields). -/
def classPair : CName := 3

/-- Test class SubPair (extends Pair, overrides setfst). -/
def classSubPair : CName := 4

/-- First field name. -/
def fstF : FName := 1

/-- Second field name. -/
def sndF : FName := 2

/-- Swap method name. -/
def swapM : MName := 1

/-- Set-first method name. -/
def setfstM : MName := 2

/-- Fresh variable for setfst parameter. -/
def newfstV : VName := 1

/-- Pair table with A, B, and Pair (T1). -/
def pairTable : ClassTable :=
  [{ name := classA, super := Object, fields := [], ctorParams := [],
     methods := [] },
   { name := classB, super := classA, fields := [], ctorParams := [],
     methods := [] },
   { name := classPair, super := Object,
     fields := [(Object, fstF), (Object, sndF)],
     ctorParams := [(Object, fstF), (Object, sndF)],
     methods :=
       [(swapM,
         { ret := classPair, params := [],
           body :=
             Expr.new classPair
               (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                 (Expr.Args.cons (Expr.fld (Expr.var thisVar) fstF)
                   Expr.Args.nil)) }),
        (setfstM,
         { ret := classPair, params := [(Object, newfstV)],
           body :=
             Expr.new classPair
               (Expr.Args.cons (Expr.var newfstV)
                 (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                   Expr.Args.nil)) })] }]

/-- SubPair table extends pairTable with overriding SubPair (T2). -/
def subPairTable : ClassTable :=
  pairTable ++
    [{ name := classSubPair, super := classPair, fields := [],
       ctorParams := [(Object, fstF), (Object, sndF)],
       methods :=
         [(setfstM,
           { ret := classPair, params := [(Object, newfstV)],
             body :=
               Expr.new classSubPair
                 (Expr.Args.cons (Expr.var newfstV)
                   (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                     Expr.Args.nil)) })] }]

/-- Table whose only class references an undeclared class in a signature. -/
def undeclaredSigTable : ClassTable :=
  [{ name := classA, super := Object, fields := [], ctorParams := [],
     methods :=
       [(swapM,
         { ret := 99, params := [(99, newfstV)],
           body := Expr.var newfstV })] }]

/-- Table whose only undeclared reference is a cast inside a method body. -/
def undeclaredBodyTable : ClassTable :=
  [{ name := classA, super := Object, fields := [], ctorParams := [],
     methods :=
       [(swapM,
         { ret := classA, params := [],
           body :=
             Expr.invk (Expr.var thisVar) swapM
               (Expr.Args.cons (Expr.cast 99 (Expr.var thisVar))
                 Expr.Args.nil) })] }]

/-- Table whose constructor parameters do not match its fields. -/
def badCtorTable : ClassTable :=
  [{ name := classA, super := Object, fields := [],
     ctorParams := [(Object, fstF)], methods := [] }]

/-- Pair table is well-formed (T3). -/
theorem pairTable_wellFormed : WellFormed pairTable := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro cd hmem
    simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases hmem with
    | inl h1 =>
      subst h1
      decide
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        subst h3
        decide
      | inr h4 =>
        subst h4
        decide
  · decide
  · intro cd hmem
    simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases hmem with
    | inl h1 =>
      subst h1
      decide
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        subst h3
        decide
      | inr h4 =>
        subst h4
        decide
  · intro cd hmem
    simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases hmem with
    | inl h1 =>
      subst h1
      decide
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        subst h3
        decide
      | inr h4 =>
        subst h4
        decide
  · intro cd hmem
    simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases hmem with
    | inl h1 =>
      subst h1
      decide
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        subst h3
        decide
      | inr h4 =>
        subst h4
        decide
  · intro C fs h
    by_cases h0 : C = Object
    · subst h0
      have hObj : fields pairTable Object = some [] := by decide
      have hEq := Option.some_inj.mp (hObj.symm.trans h)
      subst hEq
      decide
    · by_cases h1 : C = classA
      · subst h1
        have hA : fields pairTable classA = some [] := by decide
        have hEq := Option.some_inj.mp (hA.symm.trans h)
        subst hEq
        decide
      · by_cases h2 : C = classB
        · subst h2
          have hB : fields pairTable classB = some [] := by decide
          have hEq := Option.some_inj.mp (hB.symm.trans h)
          subst hEq
          decide
        · by_cases h3 : C = classPair
          · subst h3
            have hPair : fields pairTable classPair =
              some [(Object, fstF), (Object, sndF)] := by decide
            have hEq := Option.some_inj.mp (hPair.symm.trans h)
            subst hEq
            decide
          · have hNe1 : ¬ (classA == C) = true := by
              intro hEq
              have hEq2 := beq_iff_eq.mp hEq
              exact h1 hEq2.symm
            have hNe2 : ¬ (classB == C) = true := by
              intro hEq
              have hEq2 := beq_iff_eq.mp hEq
              exact h2 hEq2.symm
            have hNe3 : ¬ (classPair == C) = true := by
              intro hEq
              have hEq2 := beq_iff_eq.mp hEq
              exact h3 hEq2.symm
            have hLk : lookupClass pairTable C = none := by
              simp only [lookupClass, pairTable, List.find?, hNe1, hNe2, hNe3]
            have hSup : supers pairTable C = [C] := by
              simp only [supers, supersAux, h0, hLk, ite_false]
            have hNone : fields pairTable C = none := by
              simp only [fields, h0, hSup, hLk, ite_false, List.foldl_cons,
                List.foldl_nil]
            have hContra := hNone.symm.trans h
            cases hContra
  · intro cd hmem p hpmem
    simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases hmem with
    | inl h1 =>
      subst h1
      simp only [List.not_mem_nil] at hpmem
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        subst h3
        simp only [List.not_mem_nil] at hpmem
      | inr h4 =>
        subst h4
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
        cases hpmem with
        | inl h5 =>
          subst h5
          show override pairTable swapM Object ([], classPair)
          intro sig' hEq
          have hNone : mtype pairTable swapM Object = none := by decide
          rw [hNone] at hEq
          cases hEq
        | inr h6 =>
          subst h6
          show override pairTable setfstM Object ([Object], classPair)
          intro sig' hEq
          have hNone : mtype pairTable setfstM Object = none := by decide
          rw [hNone] at hEq
          cases hEq
  · intro cd hmem p hpmem
    simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases hmem with
    | inl h1 =>
      subst h1
      simp only [List.not_mem_nil] at hpmem
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        subst h3
        simp only [List.not_mem_nil] at hpmem
      | inr h4 =>
        subst h4
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
        cases hpmem with
        | inl h5 =>
          subst h5
          show ([] : List VName).Nodup ∧ thisVar ∉ ([] : List VName)
          exact ⟨by decide, by decide⟩
        | inr h6 =>
          subst h6
          show ([newfstV] : List VName).Nodup ∧ thisVar ∉ ([newfstV] : List VName)
          exact ⟨by decide, by decide⟩

/-- Fields of Pair are the two Object fields (T4). -/
theorem fields_pair :
    fields pairTable classPair = some [(Object, fstF), (Object, sndF)] := by decide

/-- B is a subtype of A (T5). -/
theorem subtype_B_A : Subtype pairTable classB classA := by
  have h : directExtends pairTable classB classA :=
    ⟨ClassDecl.mk classB classA [] [] [], by decide, rfl, rfl⟩
  exact Relation.ReflTransGen.single h

/-- A is not a subtype of B (T5). -/
theorem not_subtype_A_B : ¬ Subtype pairTable classA classB := by
  suffices hInv : ∀ C, Subtype pairTable classA C → C = classA ∨ C = Object by
    intro h
    have hOr := hInv classB h
    cases hOr with
    | inl heq =>
      have hNe : classB ≠ classA := by decide
      exact absurd heq hNe
    | inr heq =>
      have hNe : classB ≠ Object := by decide
      exact absurd heq hNe
  intro C h
  simp only [Subtype] at h
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hd ih =>
    cases ih with
    | inl heq =>
      rw [heq] at hd
      obtain ⟨cd, hmem, hname, hsuper⟩ := hd
      simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
      cases hmem with
      | inl h1 =>
        subst h1
        exact Or.inr hsuper.symm
      | inr h2 =>
        cases h2 with
        | inl h3 =>
          subst h3
          have hEq : classB = classA := hname
          exact absurd hEq (by decide)
        | inr h4 =>
          subst h4
          have hEq : classPair = classA := hname
          exact absurd hEq (by decide)
    | inr heq =>
      rw [heq] at hd
      obtain ⟨cd, hmem, hname, hsuper⟩ := hd
      simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
      cases hmem with
      | inl h1 =>
        subst h1
        have hEq : classA = Object := hname
        exact absurd hEq (by decide)
      | inr h2 =>
        cases h2 with
        | inl h3 =>
          subst h3
          have hEq : classB = Object := hname
          exact absurd hEq (by decide)
        | inr h4 =>
          subst h4
          have hEq : classPair = Object := hname
          exact absurd hEq (by decide)

/-- Swap evaluation exchanges the two components (T6). -/
theorem pair_swap_eval :
    Steps pairTable
      (Expr.invk
        (Expr.new classPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classB Expr.Args.nil)
              Expr.Args.nil)))
        swapM Expr.Args.nil)
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            Expr.Args.nil))) := by
  have hVA : Value (Expr.new classA Expr.Args.nil) :=
    Value.new classA Expr.Args.nil ArgsValue.nil
  have hVB : Value (Expr.new classB Expr.Args.nil) :=
    Value.new classB Expr.Args.nil ArgsValue.nil
  have hVs : ArgsValue
      (Expr.Args.cons (Expr.new classA Expr.Args.nil)
        (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil)) :=
    ArgsValue.cons hVA (ArgsValue.cons hVB ArgsValue.nil)
  have hUs : ArgsValue Expr.Args.nil := ArgsValue.nil
  have hMbody : mbody pairTable swapM classPair =
      some ([], Expr.new classPair
        (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
          (Expr.Args.cons (Expr.fld (Expr.var thisVar) fstF)
            Expr.Args.nil))) := by decide
  have hStep1 : Step pairTable
      (Expr.invk
        (Expr.new classPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classB Expr.Args.nil)
              Expr.Args.nil)))
        swapM Expr.Args.nil)
      (Expr.new classPair
        (Expr.Args.cons
          (Expr.fld
            (Expr.new classPair
              (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                (Expr.Args.cons (Expr.new classB Expr.Args.nil)
                  Expr.Args.nil)))
            sndF)
          (Expr.Args.cons
            (Expr.fld
              (Expr.new classPair
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  (Expr.Args.cons (Expr.new classB Expr.Args.nil)
                    Expr.Args.nil)))
              fstF)
            Expr.Args.nil))) :=
    Step.invk hVs hUs hMbody rfl
  have hProj1 : Step pairTable
      (Expr.fld
        (Expr.new classPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classB Expr.Args.nil)
              Expr.Args.nil)))
        sndF)
      (Expr.new classB Expr.Args.nil) :=
    Step.proj hVs fields_pair (by decide)
  have hStep2 : Step pairTable
      (Expr.new classPair
        (Expr.Args.cons
          (Expr.fld
            (Expr.new classPair
              (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                (Expr.Args.cons (Expr.new classB Expr.Args.nil)
                  Expr.Args.nil)))
            sndF)
          (Expr.Args.cons
            (Expr.fld
              (Expr.new classPair
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  (Expr.Args.cons (Expr.new classB Expr.Args.nil)
                    Expr.Args.nil)))
              fstF)
            Expr.Args.nil)))
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons
            (Expr.fld
              (Expr.new classPair
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  (Expr.Args.cons (Expr.new classB Expr.Args.nil)
                    Expr.Args.nil)))
              fstF)
            Expr.Args.nil))) :=
    Step.newArgs (ArgsStep.head hProj1)
  have hProj2 : Step pairTable
      (Expr.fld
        (Expr.new classPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classB Expr.Args.nil)
              Expr.Args.nil)))
        fstF)
      (Expr.new classA Expr.Args.nil) :=
    Step.proj hVs fields_pair (by decide)
  have hInner : ArgsStep pairTable
      (Expr.Args.cons
        (Expr.fld
          (Expr.new classPair
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              (Expr.Args.cons (Expr.new classB Expr.Args.nil)
                Expr.Args.nil)))
          fstF)
        Expr.Args.nil)
      (Expr.Args.cons (Expr.new classA Expr.Args.nil) Expr.Args.nil) :=
    ArgsStep.head hProj2
  have hTail : ArgsStep pairTable
      (Expr.Args.cons (Expr.new classB Expr.Args.nil)
        (Expr.Args.cons
          (Expr.fld
            (Expr.new classPair
              (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                (Expr.Args.cons (Expr.new classB Expr.Args.nil)
                  Expr.Args.nil)))
            fstF)
          Expr.Args.nil))
      (Expr.Args.cons (Expr.new classB Expr.Args.nil)
        (Expr.Args.cons (Expr.new classA Expr.Args.nil) Expr.Args.nil)) :=
    ArgsStep.tail hVB hInner
  have hStep3 : Step pairTable
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons
            (Expr.fld
              (Expr.new classPair
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  (Expr.Args.cons (Expr.new classB Expr.Args.nil)
                    Expr.Args.nil)))
              fstF)
            Expr.Args.nil)))
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            Expr.Args.nil))) :=
    Step.newArgs hTail
  exact Relation.ReflTransGen.head hStep1
    (Relation.ReflTransGen.head hStep2
      (Relation.ReflTransGen.head hStep3 Relation.ReflTransGen.refl))

/-- Setfst evaluation replaces the first component (T7). -/
theorem pair_setfst_eval :
    Steps pairTable
      (Expr.invk
        (Expr.new classPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              Expr.Args.nil)))
        setfstM
        (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil))
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            Expr.Args.nil))) := by
  have hVA : Value (Expr.new classA Expr.Args.nil) :=
    Value.new classA Expr.Args.nil ArgsValue.nil
  have hVB : Value (Expr.new classB Expr.Args.nil) :=
    Value.new classB Expr.Args.nil ArgsValue.nil
  have hVs : ArgsValue
      (Expr.Args.cons (Expr.new classA Expr.Args.nil)
        (Expr.Args.cons (Expr.new classA Expr.Args.nil) Expr.Args.nil)) :=
    ArgsValue.cons hVA (ArgsValue.cons hVA ArgsValue.nil)
  have hUs : ArgsValue
      (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil) :=
    ArgsValue.cons hVB ArgsValue.nil
  have hMbody : mbody pairTable setfstM classPair =
      some ([newfstV], Expr.new classPair
        (Expr.Args.cons (Expr.var newfstV)
          (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
            Expr.Args.nil))) := by decide
  have hStep1 : Step pairTable
      (Expr.invk
        (Expr.new classPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              Expr.Args.nil)))
        setfstM
        (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil))
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons
            (Expr.fld
              (Expr.new classPair
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                    Expr.Args.nil)))
              sndF)
            Expr.Args.nil))) :=
    Step.invk hVs hUs hMbody rfl
  have hProj : Step pairTable
      (Expr.fld
        (Expr.new classPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              Expr.Args.nil)))
        sndF)
      (Expr.new classA Expr.Args.nil) :=
    Step.proj hVs fields_pair (by decide)
  have hInner : ArgsStep pairTable
      (Expr.Args.cons
        (Expr.fld
          (Expr.new classPair
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                Expr.Args.nil)))
          sndF)
        Expr.Args.nil)
      (Expr.Args.cons (Expr.new classA Expr.Args.nil) Expr.Args.nil) :=
    ArgsStep.head hProj
  have hTail : ArgsStep pairTable
      (Expr.Args.cons (Expr.new classB Expr.Args.nil)
        (Expr.Args.cons
          (Expr.fld
            (Expr.new classPair
              (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  Expr.Args.nil)))
            sndF)
          Expr.Args.nil))
      (Expr.Args.cons (Expr.new classB Expr.Args.nil)
        (Expr.Args.cons (Expr.new classA Expr.Args.nil) Expr.Args.nil)) :=
    ArgsStep.tail hVB hInner
  have hStep2 : Step pairTable
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
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            Expr.Args.nil))) :=
    Step.newArgs hTail
  exact Relation.ReflTransGen.head hStep1
    (Relation.ReflTransGen.head hStep2 Relation.ReflTransGen.refl)

/-- SubPair selects the overriding setfst body (T8). -/
theorem subpair_mbody_override :
    mbody subPairTable setfstM classSubPair =
      some ([newfstV],
        Expr.new classSubPair
          (Expr.Args.cons (Expr.var newfstV)
            (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
              Expr.Args.nil))) := by
  decide

/-- SubPair setfst evaluation uses the override body (T9). -/
theorem subpair_setfst_eval :
    Steps subPairTable
      (Expr.invk
        (Expr.new classSubPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              Expr.Args.nil)))
        setfstM
        (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil))
      (Expr.new classSubPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            Expr.Args.nil))) := by
  have hVA : Value (Expr.new classA Expr.Args.nil) :=
    Value.new classA Expr.Args.nil ArgsValue.nil
  have hVB : Value (Expr.new classB Expr.Args.nil) :=
    Value.new classB Expr.Args.nil ArgsValue.nil
  have hVs : ArgsValue
      (Expr.Args.cons (Expr.new classA Expr.Args.nil)
        (Expr.Args.cons (Expr.new classA Expr.Args.nil) Expr.Args.nil)) :=
    ArgsValue.cons hVA (ArgsValue.cons hVA ArgsValue.nil)
  have hUs : ArgsValue
      (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil) :=
    ArgsValue.cons hVB ArgsValue.nil
  have hFields : fields subPairTable classSubPair =
      some [(Object, fstF), (Object, sndF)] := by decide
  have hStep1 : Step subPairTable
      (Expr.invk
        (Expr.new classSubPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              Expr.Args.nil)))
        setfstM
        (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil))
      (Expr.new classSubPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons
            (Expr.fld
              (Expr.new classSubPair
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                    Expr.Args.nil)))
              sndF)
            Expr.Args.nil))) :=
    Step.invk hVs hUs subpair_mbody_override rfl
  have hProj : Step subPairTable
      (Expr.fld
        (Expr.new classSubPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              Expr.Args.nil)))
        sndF)
      (Expr.new classA Expr.Args.nil) :=
    Step.proj hVs hFields (by decide)
  have hInner : ArgsStep subPairTable
      (Expr.Args.cons
        (Expr.fld
          (Expr.new classSubPair
            (Expr.Args.cons (Expr.new classA Expr.Args.nil)
              (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                Expr.Args.nil)))
          sndF)
        Expr.Args.nil)
      (Expr.Args.cons (Expr.new classA Expr.Args.nil) Expr.Args.nil) :=
    ArgsStep.head hProj
  have hTail : ArgsStep subPairTable
      (Expr.Args.cons (Expr.new classB Expr.Args.nil)
        (Expr.Args.cons
          (Expr.fld
            (Expr.new classSubPair
              (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  Expr.Args.nil)))
            sndF)
          Expr.Args.nil))
      (Expr.Args.cons (Expr.new classB Expr.Args.nil)
        (Expr.Args.cons (Expr.new classA Expr.Args.nil) Expr.Args.nil)) :=
    ArgsStep.tail hVB hInner
  have hStep2 : Step subPairTable
      (Expr.new classSubPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons
            (Expr.fld
              (Expr.new classSubPair
                (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                  (Expr.Args.cons (Expr.new classA Expr.Args.nil)
                    Expr.Args.nil)))
              sndF)
            Expr.Args.nil)))
      (Expr.new classSubPair
        (Expr.Args.cons (Expr.new classB Expr.Args.nil)
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            Expr.Args.nil))) :=
    Step.newArgs hTail
  exact Relation.ReflTransGen.head hStep1
    (Relation.ReflTransGen.head hStep2 Relation.ReflTransGen.refl)

/-- Method type of setfst on Pair (T10). -/
theorem mtype_setfst :
    mtype pairTable setfstM classPair = some ([Object], classPair) := by decide

/-- Missing method body lookup is none (T10). -/
theorem mbody_missing : mbody pairTable 99 classPair = none := by decide

/-- Upcast of B to A steps in one step (T11 E-CAST). -/
theorem cast_up_step :
    Step pairTable
      (Expr.cast classA (Expr.new classB Expr.Args.nil))
      (Expr.new classB Expr.Args.nil) := by
  exact Step.cast ArgsValue.nil subtype_B_A

/-- Downcast of A to B is stuck with no step (T11). -/
theorem cast_bad_stuck :
    ¬ ∃ e', Step pairTable
      (Expr.cast classB (Expr.new classA Expr.Args.nil)) e' := by
  intro h
  obtain ⟨e', hStep⟩ := h
  cases hStep with
  | cast _ hSub =>
    exact absurd hSub not_subtype_A_B
  | castCongr hInner =>
    cases hInner with
    | newArgs hArgs =>
      cases hArgs

/-- Cyclic table with 5 extends 6 and 6 extends 5 (T12). -/
def cyclicTable : ClassTable :=
  [{ name := 5, super := 6, fields := [], ctorParams := [], methods := [] },
   { name := 6, super := 5, fields := [], ctorParams := [], methods := [] }]

/-- Cyclic table is not well-formed (T12). -/
theorem cyclic_not_wellFormed : ¬ WellFormed cyclicTable := by
  intro h
  have hd := h.supersNodup (ClassDecl.mk 5 6 [] [] []) (by decide)
  exact (by decide : ¬ (supers cyclicTable 5).Nodup) hd

/-- Duplicate class table with two entries named A (T13). -/
def dupClassTable : ClassTable :=
  [{ name := classA, super := Object, fields := [], ctorParams := [],
     methods := [] },
   { name := classA, super := Object, fields := [], ctorParams := [],
     methods := [] }]

/-- Duplicate class table is not well-formed (T13). -/
theorem dupClass_not_wellFormed : ¬ WellFormed dupClassTable := by
  intro h
  have hd := h.namesNodup
  exact (by decide : ¬ (dupClassTable.map ClassDecl.name).Nodup) hd

/-- Duplicate method table with A replaced by dup-method entry (T14). -/
def dupMethodTable : ClassTable :=
  [{ name := classA, super := Object, fields := [], ctorParams := [],
     methods :=
       [(swapM,
         { ret := classA, params := [], body := Expr.var thisVar }),
        (swapM,
         { ret := classA, params := [], body := Expr.var thisVar })] },
   { name := classB, super := classA, fields := [], ctorParams := [],
     methods := [] },
   { name := classPair, super := Object,
     fields := [(Object, fstF), (Object, sndF)],
     ctorParams := [(Object, fstF), (Object, sndF)],
     methods :=
       [(swapM,
         { ret := classPair, params := [],
           body :=
             Expr.new classPair
               (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                 (Expr.Args.cons (Expr.fld (Expr.var thisVar) fstF)
                   Expr.Args.nil)) }),
        (setfstM,
         { ret := classPair, params := [(Object, newfstV)],
           body :=
             Expr.new classPair
               (Expr.Args.cons (Expr.var newfstV)
                 (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                   Expr.Args.nil)) })] }]

/-- Duplicate method table is not well-formed (T14). -/
theorem dupMethod_not_wellFormed : ¬ WellFormed dupMethodTable := by
  intro h
  have hd := h.methodNamesNodup (ClassDecl.mk classA Object [] []
    [(swapM, { ret := classA, params := [], body := Expr.var thisVar }),
      (swapM, { ret := classA, params := [], body := Expr.var thisVar })])
    (by decide)
  exact (by decide : ¬ ([swapM, swapM]).Nodup) hd

/-- Swap expression typechecks at Pair in the empty context (T15). -/
theorem typing_pair_swap :
    Typing pairTable (fun _ => none)
      (Expr.invk
        (Expr.new classPair
          (Expr.Args.cons (Expr.new classA Expr.Args.nil)
            (Expr.Args.cons (Expr.new classB Expr.Args.nil)
              Expr.Args.nil)))
        swapM Expr.Args.nil)
      classPair := by
  have hAO : Subtype pairTable classA Object :=
    Relation.ReflTransGen.single
      ⟨ClassDecl.mk classA Object [] [] [], by decide, rfl, rfl⟩
  have hBO : Subtype pairTable classB Object :=
    Relation.ReflTransGen.trans subtype_B_A hAO
  have hFA : fields pairTable classA = some [] := by decide
  have hFB : fields pairTable classB = some [] := by decide
  have hM : mtype pairTable swapM classPair = some ([], classPair) := by decide
  have hA : Typing pairTable (fun _ => none) (Expr.new classA Expr.Args.nil)
      classA :=
    Typing.new hFA ArgsTyping.nil
  have hB : Typing pairTable (fun _ => none) (Expr.new classB Expr.Args.nil)
      classB :=
    Typing.new hFB ArgsTyping.nil
  have hRecv : Typing pairTable (fun _ => none)
      (Expr.new classPair
        (Expr.Args.cons (Expr.new classA Expr.Args.nil)
          (Expr.Args.cons (Expr.new classB Expr.Args.nil) Expr.Args.nil)))
      classPair :=
    Typing.new fields_pair
      (ArgsTyping.cons hA hAO (ArgsTyping.cons hB hBO ArgsTyping.nil))
  exact Typing.invk hRecv hM ArgsTyping.nil

/-- Undeclared signature class is not well-formed. -/
theorem undeclaredSig_not_wellFormed : ¬ WellFormed undeclaredSigTable := by
  intro h
  have hd := h.refsDeclared (ClassDecl.mk classA Object [] []
    [(swapM,
      { ret := 99, params := [(99, newfstV)],
        body := Expr.var newfstV })]) (by decide) 99 (by decide)
  exact (by decide : ¬ (99 = Object ∨
    ∃ d ∈ undeclaredSigTable, d.name = 99)) hd

/-- Undeclared class inside a method body is not well-formed. -/
theorem undeclaredBody_not_wellFormed : ¬ WellFormed undeclaredBodyTable := by
  intro h
  have hd := h.refsDeclared (ClassDecl.mk classA Object [] []
    [(swapM,
      { ret := classA, params := [],
        body :=
          Expr.invk (Expr.var thisVar) swapM
            (Expr.Args.cons (Expr.cast 99 (Expr.var thisVar))
              Expr.Args.nil) })]) (by decide) 99 (by decide)
  exact (by decide : ¬ (99 = Object ∨
    ∃ d ∈ undeclaredBodyTable, d.name = 99)) hd

/-- Pair table classes are ok. -/
theorem pairTable_tableOk : TableOk pairTable := by
  intro cd hmem
  simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
  cases hmem with
  | inl h1 =>
    subst h1
    refine ⟨?_, ?_⟩
    · exact ⟨[], by decide, rfl⟩
    · intro p hpmem
      simp only [List.not_mem_nil] at hpmem
  | inr h2 =>
    cases h2 with
    | inl h3 =>
      subst h3
      refine ⟨?_, ?_⟩
      · exact ⟨[], by decide, rfl⟩
      · intro p hpmem
        simp only [List.not_mem_nil] at hpmem
    | inr h4 =>
      subst h4
      refine ⟨?_, ?_⟩
      · exact ⟨[], by decide, rfl⟩
      · intro p hpmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
        cases hpmem with
        | inl h5 =>
          subst h5
          refine ⟨?_, ?_⟩
          · refine ⟨classPair, ?_, ?_⟩
            · have hCtxThis : contextOf classPair [] thisVar =
                some classPair := by decide
              have hThis : Typing pairTable (contextOf classPair [])
                (Expr.var thisVar) classPair :=
                Typing.var hCtxThis
              have hSndMem : (Object, sndF) ∈
                [(Object, fstF), (Object, sndF)] := by decide
              have hFstMem : (Object, fstF) ∈
                [(Object, fstF), (Object, sndF)] := by decide
              have hSnd : Typing pairTable (contextOf classPair [])
                (Expr.fld (Expr.var thisVar) sndF) Object :=
                Typing.field hThis fields_pair hSndMem
              have hFst : Typing pairTable (contextOf classPair [])
                (Expr.fld (Expr.var thisVar) fstF) Object :=
                Typing.field hThis fields_pair hFstMem
              have hSubR : Subtype pairTable Object Object :=
                Relation.ReflTransGen.refl
              have hArgs : ArgsTyping pairTable (contextOf classPair [])
                (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                  (Expr.Args.cons (Expr.fld (Expr.var thisVar) fstF)
                    Expr.Args.nil)) [Object, Object] :=
                ArgsTyping.cons hSnd hSubR
                  (ArgsTyping.cons hFst hSubR ArgsTyping.nil)
              exact Typing.new fields_pair hArgs
            · exact Relation.ReflTransGen.refl
          · show override pairTable swapM Object ([], classPair)
            intro sig' hEq
            have hNone : mtype pairTable swapM Object = none := by decide
            rw [hNone] at hEq
            cases hEq
        | inr h6 =>
          subst h6
          refine ⟨?_, ?_⟩
          · refine ⟨classPair, ?_, ?_⟩
            · have hCtxNew : contextOf classPair [(Object, newfstV)]
                newfstV = some Object := by decide
              have hNew : Typing pairTable
                (contextOf classPair [(Object, newfstV)])
                (Expr.var newfstV) Object :=
                Typing.var hCtxNew
              have hCtxThis2 : contextOf classPair [(Object, newfstV)]
                thisVar = some classPair := by decide
              have hThis2 : Typing pairTable
                (contextOf classPair [(Object, newfstV)])
                (Expr.var thisVar) classPair :=
                Typing.var hCtxThis2
              have hSndMem2 : (Object, sndF) ∈
                [(Object, fstF), (Object, sndF)] := by decide
              have hSnd2 : Typing pairTable
                (contextOf classPair [(Object, newfstV)])
                (Expr.fld (Expr.var thisVar) sndF) Object :=
                Typing.field hThis2 fields_pair hSndMem2
              have hSubR2 : Subtype pairTable Object Object :=
                Relation.ReflTransGen.refl
              have hArgs2 : ArgsTyping pairTable
                (contextOf classPair [(Object, newfstV)])
                (Expr.Args.cons (Expr.var newfstV)
                  (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                    Expr.Args.nil)) [Object, Object] :=
                ArgsTyping.cons hNew hSubR2
                  (ArgsTyping.cons hSnd2 hSubR2 ArgsTyping.nil)
              exact Typing.new fields_pair hArgs2
            · exact Relation.ReflTransGen.refl
          · show override pairTable setfstM Object ([Object], classPair)
            intro sig' hEq
            have hNone : mtype pairTable setfstM Object = none := by decide
            rw [hNone] at hEq
            cases hEq

/-- SubPair table is well-formed. -/
theorem subPairTable_wellFormed : WellFormed subPairTable := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro cd hmem
    simp only [subPairTable, List.mem_append] at hmem
    cases hmem with
    | inl hLeft =>
      simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hLeft
      cases hLeft with
      | inl h1 =>
        subst h1
        decide
      | inr h2 =>
        cases h2 with
        | inl h3 =>
          subst h3
          decide
        | inr h4 =>
          subst h4
          decide
    | inr hRight =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRight
      subst hRight
      decide
  · decide
  · intro cd hmem
    simp only [subPairTable, List.mem_append] at hmem
    cases hmem with
    | inl hLeft =>
      simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hLeft
      cases hLeft with
      | inl h1 =>
        subst h1
        decide
      | inr h2 =>
        cases h2 with
        | inl h3 =>
          subst h3
          decide
        | inr h4 =>
          subst h4
          decide
    | inr hRight =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRight
      subst hRight
      decide
  · intro cd hmem
    simp only [subPairTable, List.mem_append] at hmem
    cases hmem with
    | inl hLeft =>
      simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hLeft
      cases hLeft with
      | inl h1 =>
        subst h1
        decide
      | inr h2 =>
        cases h2 with
        | inl h3 =>
          subst h3
          decide
        | inr h4 =>
          subst h4
          decide
    | inr hRight =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRight
      subst hRight
      decide
  · intro cd hmem
    simp only [subPairTable, List.mem_append] at hmem
    cases hmem with
    | inl hLeft =>
      simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hLeft
      cases hLeft with
      | inl h1 =>
        subst h1
        decide
      | inr h2 =>
        cases h2 with
        | inl h3 =>
          subst h3
          decide
        | inr h4 =>
          subst h4
          decide
    | inr hRight =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRight
      subst hRight
      decide
  · intro C fs h
    by_cases h0 : C = Object
    · subst h0
      have hObj : fields subPairTable Object = some [] := by decide
      have hEq := Option.some_inj.mp (hObj.symm.trans h)
      subst hEq
      decide
    · by_cases h1 : C = classA
      · subst h1
        have hA : fields subPairTable classA = some [] := by decide
        have hEq := Option.some_inj.mp (hA.symm.trans h)
        subst hEq
        decide
      · by_cases h2 : C = classB
        · subst h2
          have hB : fields subPairTable classB = some [] := by decide
          have hEq := Option.some_inj.mp (hB.symm.trans h)
          subst hEq
          decide
        · by_cases h3 : C = classPair
          · subst h3
            have hPair : fields subPairTable classPair =
              some [(Object, fstF), (Object, sndF)] := by decide
            have hEq := Option.some_inj.mp (hPair.symm.trans h)
            subst hEq
            decide
          · by_cases h4 : C = classSubPair
            · subst h4
              have hSub : fields subPairTable classSubPair =
                some [(Object, fstF), (Object, sndF)] := by decide
              have hEq := Option.some_inj.mp (hSub.symm.trans h)
              subst hEq
              decide
            · have hNe1 : ¬ (classA == C) = true := by
                intro hEq
                have hEq2 := beq_iff_eq.mp hEq
                exact h1 hEq2.symm
              have hNe2 : ¬ (classB == C) = true := by
                intro hEq
                have hEq2 := beq_iff_eq.mp hEq
                exact h2 hEq2.symm
              have hNe3 : ¬ (classPair == C) = true := by
                intro hEq
                have hEq2 := beq_iff_eq.mp hEq
                exact h3 hEq2.symm
              have hNe4 : ¬ (classSubPair == C) = true := by
                intro hEq
                have hEq2 := beq_iff_eq.mp hEq
                exact h4 hEq2.symm
              have hLk : lookupClass subPairTable C = none := by
                simp only [lookupClass, subPairTable, pairTable, List.cons_append,
                  List.nil_append, List.find?, hNe1, hNe2, hNe3, hNe4]
              have hSup : supers subPairTable C = [C] := by
                simp only [supers, supersAux, h0, hLk, ite_false]
              have hNone : fields subPairTable C = none := by
                simp only [fields, h0, hSup, hLk, ite_false, List.foldl_cons,
                  List.foldl_nil]
              have hContra := hNone.symm.trans h
              cases hContra
  · intro cd hmem p hpmem
    simp only [subPairTable, List.mem_append] at hmem
    cases hmem with
    | inl hLeft =>
      simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hLeft
      cases hLeft with
      | inl h1 =>
        subst h1
        simp only [List.not_mem_nil] at hpmem
      | inr h2 =>
        cases h2 with
        | inl h3 =>
          subst h3
          simp only [List.not_mem_nil] at hpmem
        | inr h4 =>
          subst h4
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
          cases hpmem with
          | inl h5 =>
            subst h5
            show override subPairTable swapM Object ([], classPair)
            intro sig' hEq
            have hNone : mtype subPairTable swapM Object = none := by decide
            rw [hNone] at hEq
            cases hEq
          | inr h6 =>
            subst h6
            show override subPairTable setfstM Object ([Object], classPair)
            intro sig' hEq
            have hNone : mtype subPairTable setfstM Object = none := by decide
            rw [hNone] at hEq
            cases hEq
    | inr hRight =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRight
      subst hRight
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
      subst hpmem
      show override subPairTable setfstM classPair ([Object], classPair)
      intro sig' hEq
      have hM : mtype subPairTable setfstM classPair =
        some ([Object], classPair) := by decide
      rw [hM] at hEq
      exact (Option.some_inj.mp hEq).symm
  · intro cd hmem p hpmem
    simp only [subPairTable, List.mem_append] at hmem
    cases hmem with
    | inl hLeft =>
      simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hLeft
      cases hLeft with
      | inl h1 =>
        subst h1
        simp only [List.not_mem_nil] at hpmem
      | inr h2 =>
        cases h2 with
        | inl h3 =>
          subst h3
          simp only [List.not_mem_nil] at hpmem
        | inr h4 =>
          subst h4
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
          cases hpmem with
          | inl h5 =>
            subst h5
            show ([] : List VName).Nodup ∧ thisVar ∉ ([] : List VName)
            exact ⟨by decide, by decide⟩
          | inr h6 =>
            subst h6
            show ([newfstV] : List VName).Nodup ∧ thisVar ∉ ([newfstV] : List VName)
            exact ⟨by decide, by decide⟩
    | inr hRight =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRight
      subst hRight
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
      subst hpmem
      show ([newfstV] : List VName).Nodup ∧ thisVar ∉ ([newfstV] : List VName)
      exact ⟨by decide, by decide⟩

/-- SubPair table classes are ok. -/
theorem subPairTable_tableOk : TableOk subPairTable := by
  intro cd hmem
  simp only [subPairTable, List.mem_append] at hmem
  cases hmem with
  | inl hLeft =>
    simp only [pairTable, List.mem_cons, List.not_mem_nil, or_false] at hLeft
    cases hLeft with
    | inl h1 =>
      subst h1
      refine ⟨?_, ?_⟩
      · exact ⟨[], by decide, rfl⟩
      · intro p hpmem
        simp only [List.not_mem_nil] at hpmem
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        subst h3
        refine ⟨?_, ?_⟩
        · exact ⟨[], by decide, rfl⟩
        · intro p hpmem
          simp only [List.not_mem_nil] at hpmem
      | inr h4 =>
        subst h4
        refine ⟨?_, ?_⟩
        · exact ⟨[], by decide, rfl⟩
        · intro p hpmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
          have hFieldsPair : fields subPairTable classPair =
              some [(Object, fstF), (Object, sndF)] := by decide
          cases hpmem with
          | inl h5 =>
            subst h5
            refine ⟨?_, ?_⟩
            · refine ⟨classPair, ?_, ?_⟩
              · have hCtxThis : contextOf classPair [] thisVar =
                  some classPair := by decide
                have hThis : Typing subPairTable (contextOf classPair [])
                  (Expr.var thisVar) classPair :=
                  Typing.var hCtxThis
                have hSndMem : (Object, sndF) ∈
                  [(Object, fstF), (Object, sndF)] := by decide
                have hFstMem : (Object, fstF) ∈
                  [(Object, fstF), (Object, sndF)] := by decide
                have hSnd : Typing subPairTable (contextOf classPair [])
                  (Expr.fld (Expr.var thisVar) sndF) Object :=
                  Typing.field hThis hFieldsPair hSndMem
                have hFst : Typing subPairTable (contextOf classPair [])
                  (Expr.fld (Expr.var thisVar) fstF) Object :=
                  Typing.field hThis hFieldsPair hFstMem
                have hSubR : Subtype subPairTable Object Object :=
                  Relation.ReflTransGen.refl
                have hArgs : ArgsTyping subPairTable (contextOf classPair [])
                  (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                    (Expr.Args.cons (Expr.fld (Expr.var thisVar) fstF)
                      Expr.Args.nil)) [Object, Object] :=
                  ArgsTyping.cons hSnd hSubR
                    (ArgsTyping.cons hFst hSubR ArgsTyping.nil)
                exact Typing.new hFieldsPair hArgs
              · exact Relation.ReflTransGen.refl
            · show override subPairTable swapM Object ([], classPair)
              intro sig' hEq
              have hNone : mtype subPairTable swapM Object = none := by decide
              rw [hNone] at hEq
              cases hEq
          | inr h6 =>
            subst h6
            refine ⟨?_, ?_⟩
            · refine ⟨classPair, ?_, ?_⟩
              · have hCtxNew : contextOf classPair [(Object, newfstV)]
                  newfstV = some Object := by decide
                have hNew : Typing subPairTable
                  (contextOf classPair [(Object, newfstV)])
                  (Expr.var newfstV) Object :=
                  Typing.var hCtxNew
                have hCtxThis2 : contextOf classPair [(Object, newfstV)]
                  thisVar = some classPair := by decide
                have hThis2 : Typing subPairTable
                  (contextOf classPair [(Object, newfstV)])
                  (Expr.var thisVar) classPair :=
                  Typing.var hCtxThis2
                have hSndMem2 : (Object, sndF) ∈
                  [(Object, fstF), (Object, sndF)] := by decide
                have hSnd2 : Typing subPairTable
                  (contextOf classPair [(Object, newfstV)])
                  (Expr.fld (Expr.var thisVar) sndF) Object :=
                  Typing.field hThis2 hFieldsPair hSndMem2
                have hSubR2 : Subtype subPairTable Object Object :=
                  Relation.ReflTransGen.refl
                have hArgs2 : ArgsTyping subPairTable
                  (contextOf classPair [(Object, newfstV)])
                  (Expr.Args.cons (Expr.var newfstV)
                    (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                      Expr.Args.nil)) [Object, Object] :=
                  ArgsTyping.cons hNew hSubR2
                    (ArgsTyping.cons hSnd2 hSubR2 ArgsTyping.nil)
                exact Typing.new hFieldsPair hArgs2
              · exact Relation.ReflTransGen.refl
            · show override subPairTable setfstM Object ([Object], classPair)
              intro sig' hEq
              have hNone : mtype subPairTable setfstM Object = none := by decide
              rw [hNone] at hEq
              cases hEq
  | inr hRight =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRight
    subst hRight
    refine ⟨?_, ?_⟩
    · exact ⟨[(Object, fstF), (Object, sndF)], by decide, rfl⟩
    · intro p hpmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
      subst hpmem
      refine ⟨?_, ?_⟩
      · refine ⟨classSubPair, ?_, ?_⟩
        · have hCtxNewS : contextOf classSubPair [(Object, newfstV)]
            newfstV = some Object := by decide
          have hNewS : Typing subPairTable
            (contextOf classSubPair [(Object, newfstV)])
            (Expr.var newfstV) Object :=
            Typing.var hCtxNewS
          have hCtxThisS : contextOf classSubPair [(Object, newfstV)]
            thisVar = some classSubPair := by decide
          have hThisS : Typing subPairTable
            (contextOf classSubPair [(Object, newfstV)])
            (Expr.var thisVar) classSubPair :=
            Typing.var hCtxThisS
          have hFieldsSub : fields subPairTable classSubPair =
            some [(Object, fstF), (Object, sndF)] := by decide
          have hSndMemS : (Object, sndF) ∈
            [(Object, fstF), (Object, sndF)] := by decide
          have hSndS : Typing subPairTable
            (contextOf classSubPair [(Object, newfstV)])
            (Expr.fld (Expr.var thisVar) sndF) Object :=
            Typing.field hThisS hFieldsSub hSndMemS
          have hSubRS : Subtype subPairTable Object Object :=
            Relation.ReflTransGen.refl
          have hArgsS : ArgsTyping subPairTable
            (contextOf classSubPair [(Object, newfstV)])
            (Expr.Args.cons (Expr.var newfstV)
              (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                Expr.Args.nil)) [Object, Object] :=
            ArgsTyping.cons hNewS hSubRS
              (ArgsTyping.cons hSndS hSubRS ArgsTyping.nil)
          exact Typing.new hFieldsSub hArgsS
        · have hExt : directExtends subPairTable classSubPair classPair :=
            ⟨ClassDecl.mk classSubPair classPair []
              [(Object, fstF), (Object, sndF)]
              [(setfstM,
                { ret := classPair, params := [(Object, newfstV)],
                  body :=
                    Expr.new classSubPair
                      (Expr.Args.cons (Expr.var newfstV)
                        (Expr.Args.cons (Expr.fld (Expr.var thisVar) sndF)
                          Expr.Args.nil)) })],
              by decide, rfl, rfl⟩
          exact Relation.ReflTransGen.single hExt
      · show override subPairTable setfstM classPair ([Object], classPair)
        intro sig' hEq
        have hM : mtype subPairTable setfstM classPair =
          some ([Object], classPair) := by decide
        rw [hM] at hEq
        exact (Option.some_inj.mp hEq).symm

/-- Pair table is valid. -/
theorem pairTable_valid : ValidTable pairTable :=
  ⟨pairTable_wellFormed, pairTable_tableOk⟩

/-- SubPair table is valid. -/
theorem subPairTable_valid : ValidTable subPairTable :=
  ⟨subPairTable_wellFormed, subPairTable_tableOk⟩

/-- Cyclic table is not valid. -/
theorem cyclic_not_valid : ¬ ValidTable cyclicTable := by
  exact fun h => cyclic_not_wellFormed h.1

/-- Bad-constructor table is not valid. -/
theorem badCtor_not_valid : ¬ ValidTable badCtorTable := by
  intro h
  have hOk := h.2 (ClassDecl.mk classA Object [] [(Object, fstF)] [])
    (by decide)
  obtain ⟨fs, hFields, hCtor⟩ := hOk.1
  have hObj : fields badCtorTable Object = some [] := by decide
  have hEq : fs = [] := Option.some_inj.mp (hFields.symm.trans hObj)
  subst hEq
  exact (by decide : ¬ ([(Object, fstF)] = [] ++ [])) hCtor

end Tests
end Cslib.FeatherweightJava
