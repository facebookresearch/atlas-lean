# Model checking one-counter automata against freeze LTL is Σ¹₁-complete

Checking whether some run of a nondeterministic one-counter automaton satisfies a sentence of LTL with registers is Σ¹₁-complete over infinite runs and Σ⁰₁-complete over finite runs, already for one register, the operators next and eventually, and no propositions.

**Setting.** A *one-counter automaton* $\mathcal A=(Q,q_I,\delta,F)$ has finitely many states $Q$, an initial state $q_I$, accepting states $F\subseteq Q$ and transitions $\delta\subseteq Q\times\{\mathtt{inc},\mathtt{dec},\mathtt{ifzero}\}\times Q$ acting on a counter in $\mathbb N$: $\mathtt{inc}$ adds $1$, $\mathtt{dec}$ subtracts $1$ when the result stays in $\mathbb N$, and $\mathtt{ifzero}$ requires the counter to be $0$. Runs start in $(q_I,0)$; a finite run is accepting if it ends in $F$, an infinite one if it visits $F$ infinitely often. A run is read as a data word whose letters are states and whose data values are the counter values. *LTL with registers* (freeze LTL) extends [LTL](../linear-temporal-logic/formula.md), with atoms that are states, by registers $r$: the *freeze* formula ${\downarrow_r}\varphi$ stores the current counter value in $r$ and evaluates $\varphi$, and the atom ${\uparrow_r}$ holds when the current counter value equals the value stored in $r$. The *existential model checking problem* asks, given $\mathcal A$ and a sentence $\varphi$, whether some accepting run $\rho$ satisfies $\rho,0\models\varphi$; the *pure* version allows no atoms other than ${\uparrow_r}$.

**Theorem (Demri, Lazić and Sangnier).**

1. For nondeterministic one-counter automata and sentences of LTL with registers that use only the next and eventually operators, model checking over infinite accepting runs is $\Sigma^1_1$-complete, and over finite accepting runs $\Sigma^0_1$-complete, already with one register (Theorems 18 and 17), and so are the pure versions with one register (Theorem 19).
2. For weakly deterministic one-counter automata, in which no two transitions from a state carry the same instruction, model checking pure one-register LTL with registers, with all its temporal operators, is $\Sigma^1_1$-complete over infinite runs and $\Sigma^0_1$-complete over finite runs (Theorem 21; its proof translates the next operator into an until).

Model checking first-order logic with data equality over runs of one-counter automata is $\Sigma^1_1$-complete over infinite runs and $\Sigma^0_1$-complete over finite runs, already for two variables without the successor predicate, and for four variables without state predicates (Corollary 20).

By contrast, over deterministic one-counter automata, model checking these logics is PSPACE-complete (Theorems 14 and 15, Corollary 16), and finitary satisfiability of one-register freeze LTL is decidable (Theorem 1, due to Demri and Lazić).

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The finitary bound reduces the halting problem for Minsky machines, the infinitary one their recurrence problem. The one-register freeze formula describes a run of the Minsky machine, coding counter values by repetitions of data values, as in the Demri–Lazić reduction for satisfiability; that reduction alone allows incrementing errors, because the logic cannot say that each decremented datum occurred earlier, and the one-counter automaton is used to exclude such faulty decrements. A purification lemma (Lemma 5 of the source) removes state atoms. The upper bounds hold because a finite accepting run is coded by a natural number, and an infinite one by a function $\mathbb N\to\mathbb N$ whose conditions are arithmetical. A good expansion links pages for the analytical hierarchy, its level $\Sigma^1_1$ and the reductions that define hardness for it, which the statement uses.

## Sources

- S. Demri, R. Lazić and A. Sangnier, "Model checking memoryful linear-time logics over one-counter automata", *Theoretical Computer Science* 411(22–24), pp. 2298–2316, 2010, doi:[10.1016/j.tcs.2010.02.021](https://doi.org/10.1016/j.tcs.2010.02.021); read in arXiv:0810.5517v2 ([arXiv](https://arxiv.org/abs/0810.5517v2)), whose numbering is used: the definitions of one-counter automata, LTL with registers and the model checking problems, Theorem 1, Lemma 5 (purification), Theorems 14 and 15 and Corollary 16 (deterministic automata), Theorems 17–19, Corollary 20 and Theorem 21.
