# Model checking HyperMTL with a quantifier alternation is undecidable

For HyperMTL, the extension of metric temporal logic by quantifiers over timed traces, model checking timed automata is undecidable for the fragments ∃*∀*-HyperMTL and ∀*∃*-HyperMTL, under both the asynchronous and the synchronous semantics, even with very restricted timing constraints.

**Setting.** A *trace* here is a finite timed word $(\sigma_1,\tau_1)\cdots(\sigma_n,\tau_n)$ over $\Sigma=2^{AP}$ with strictly increasing timestamps $\tau_i\in\mathbb R_{\ge0}$ (finite versions of the [timed words](../../../TheoryOfComputation/omega-automata-and-games/timed-automata/timed-words-and-timed-languages.md) read by timed automata). A *timed automaton* has finitely many locations, real-valued clocks, transitions guarded by comparisons of clocks with natural constants and resetting clocks, and accepting locations; its timed language $\llbracket\mathcal A\rrbracket$ is the set of traces it accepts. Formulas of *HyperMTL* are

$$
\phi::=\exists\pi\,\phi\mid\forall\pi\,\phi\mid\psi,\qquad\psi::=\top\mid\top_\pi\mid p_\pi\mid\psi\wedge\psi\mid\neg\psi\mid\psi\,\mathsf U_I\,\psi\mid\psi\,\mathsf S_I\,\psi,
$$

with trace variables $\pi$, propositions $p\in AP$ and non-singular intervals $I$ with endpoints in $\mathbb N\cup\{\infty\}$; $p_\pi$ holds at time $t$ when trace $\pi$ has an event at $t$ containing $p$, $\top_\pi$ when $\pi$ has an event at $t$, and $\top$ when some trace assigned so far has an event at $t$; the operators $\mathsf U_I$ and $\mathsf S_I$ range only over such event times (as in the source's MTL semantics, Section 2), so $\top$ is not constant truth. In the *asynchronous semantics* quantifiers range over all traces of the set; in the *synchronous semantics* each newly quantified trace must have its events at exactly the times of the traces already quantified. *Model checking* asks whether $\llbracket\mathcal A\rrbracket$ satisfies a closed HyperMTL formula. HyperMTL extends [HyperLTL](hyperltl.md) to timed traces.

**Theorem (Ho, Zhou and Jones).**

1. Model checking $\exists^*\forall^*$-HyperMTL and $\forall^*\exists^*$-HyperMTL is undecidable in the asynchronous semantics (Theorem 11).
2. The same holds in the synchronous semantics, with a model that uses a single clock (Theorem 12); the reduction there uses the quantifier prefix $\exists\forall\forall$, and the source does not settle the prefix $\exists\forall$ in the synchronous semantics, listing some $\exists\forall$ cases (a one-clock model with an untimed quantifier-free part) among the decidable ones (Section 5); and $\exists^*\forall^*$-HyperMTL model checking stays undecidable in the synchronous semantics for an untimed model when the quantifier-free part translates into a metric interval automaton (Proposition 15).

Alternation-free model checking is decidable, as is model checking with alternations under certain conditions in the synchronous semantics or when the time domain is bounded. Satisfiability behaves as for HyperLTL: it is decidable for formulas without a $\forall\exists$ pattern and undecidable for $\forall\exists$-HyperMTL.

## Depends on

- [HyperLTL](hyperltl.md)
- [Timed words and timed languages](../../../TheoryOfComputation/omega-automata-and-games/timed-automata/timed-words-and-timed-languages.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proofs reduce the halting problem for deterministic channel machines, finite automata with one unbounded FIFO channel, which is undecidable (Brand and Zafiropulo). The model generates candidate executions, one trace writing messages and another reading them, and a formula with one alternation uses the timestamps to match each read with an earlier write of the same message in FIFO order; in the synchronous semantics a single clock and an extra trace quantifier recreate the matching. A good expansion links a page for the undecidability of halting for deterministic channel machines.

## Sources

- H.-M. Ho, R. Zhou and T. M. Jones, "On verifying timed hyperproperties", in *26th International Symposium on Temporal Representation and Reasoning (TIME 2019)*, Leibniz International Proceedings in Informatics 147, paper 20, 2019, doi:[10.4230/LIPIcs.TIME.2019.20](https://doi.org/10.4230/LIPIcs.TIME.2019.20); read in arXiv:1812.10005v1 ([arXiv](https://arxiv.org/abs/1812.10005v1)), whose numbering is used: the definitions of timed words, timed automata, HyperMTL and its two semantics in Section 2, Lemmas 5–8 and Theorem 9 (satisfiability), Theorems 10–12 (model checking), and Propositions 13–16 (decidable subcases and untimed models).
- H.-M. Ho, R. Zhou and T. M. Jones, "Timed hyperproperties", *Information and Computation* 280, article 104639, 2021, doi:[10.1016/j.ic.2020.104639](https://doi.org/10.1016/j.ic.2020.104639), the journal version.
