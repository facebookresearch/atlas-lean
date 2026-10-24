---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.encStk_update
---

# Enc Stk update

The coded step. -/
noncomputable def stepC (c : CodedCfg tm) : Option (CodedCfg tm) :=
  c.1.map fun l ↦ stepAuxC tm (tm.m l) c.2.1 c.2.2

/-! ### The coded step is primitive recursive -/

theorem primrec₂_readTop {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ} :
    Primrec₂ fun (v : tm.σ) (S : tm.K → List ℕ) ↦ f v (readTop tm k S) := by
  have hG : Primrec₂ fun (v : tm.σ) (o : Option ℕ) ↦ f v (o.bind (decode tm k)) := by
    refine Primrec.option_casesOn (o := fun p : tm.σ × Option ℕ ↦ p.2) Primrec.snd
      ((Primrec.dom_finite fun v ↦ f v none).comp Primrec.fst) ?_ |>.of_eq fun p ↦ by
        cases p.2 <;> rfl
    exact (primrec₂_of_eventually_const (g := fun v c ↦ f v (decode tm k c))
      (symList tm k).length fun v c hc ↦ by
        rw [decode_eq_none tm hc, decode_eq_none tm le_rfl]).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact hG.comp Primrec.fst (Primrec.list_head?.comp ((primrec_arrow_eval k).comp Primrec.snd))

theorem primrec₂_stepAuxC (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    Primrec₂ (stepAuxC tm q) := by
  induction q with
  | push k f q ih =>
    exact ih.comp Primrec.fst ((primrec_arrow_update k).comp Primrec.snd
      (Primrec.list_cons.comp ((Primrec.dom_finite fun v ↦ code tm k (f v)).comp Primrec.fst)
        ((primrec_arrow_eval k).comp Primrec.snd)))
  | peek k f q ih => exact ih.comp (primrec₂_readTop tm) Primrec.snd
  | pop k f q ih =>
    exact ih.comp (primrec₂_readTop tm) ((primrec_arrow_update k).comp Primrec.snd
      (Primrec.list_tail.comp ((primrec_arrow_eval k).comp Primrec.snd)))
  | load a q ih => exact ih.comp ((Primrec.dom_finite a).comp Primrec.fst) Primrec.snd
  | branch f q₁ q₂ ih₁ ih₂ =>
    exact Primrec.cond ((Primrec.dom_finite f).comp Primrec.fst) ih₁ ih₂
  | goto f =>
    exact Primrec.pair (Primrec.option_some.comp ((Primrec.dom_finite f).comp Primrec.fst))
      (Primrec.pair Primrec.fst Primrec.snd)
  | halt => exact Primrec.pair (Primrec.const none) (Primrec.pair Primrec.fst Primrec.snd)

theorem primrec_stepC : Primrec (stepC tm) := by
  have h : Primrec₂ fun (l : tm.Λ) (p : tm.σ × (tm.K → List ℕ)) ↦ stepAuxC tm (tm.m l) p.1 p.2 :=
    primrec₂_of_finite_left fun l ↦ primrec₂_stepAuxC tm (tm.m l)
  exact Primrec.option_map Primrec.fst (h.comp Primrec.snd (Primrec.snd.comp Primrec.fst))

/-! ### The coded step simulates the machine

## Depends on

- [Code](../part-01/code.md)
- [Enc Stk](../part-01/enc-stk.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.OfTM2](../../../../../../../sources/v2/MathlibExt.md)
