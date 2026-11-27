# Single-trace satisfiability of asynchronous HyperLTL is Σ¹₁-hard

Whether an asynchronous HyperLTL sentence, which compares traces along fair trajectories that advance them at independent speeds, has a model consisting of one single trace is $\Sigma^1_1$-hard, although single-trace satisfiability of synchronous HyperLTL is just LTL satisfiability.

**Logic.** Traces are infinite words over $2^{AP}$. Asynchronous HyperLTL (A-HLTL) sentences are $Q_1 x_1 \cdots Q_n x_n\, \psi$ with trace quantifiers $Q_i \in \{\exists, \forall\}$ and $\psi$ of the form $\mathsf{E}\theta$ or $\mathsf{A}\theta$, where $\theta$ is a quantifier-free formula of [HyperLTL](../hyperltl.md), built from atoms $p_x$ with $\neg$, $\vee$, $\mathsf{X}$ and $\mathsf{U}$. A *trajectory* over a nonempty set $V$ of trace variables is an infinite sequence $t$ of nonempty subsets of $V$; it is *fair* if every $x \in V$ belongs to $t(i)$ for infinitely many $i$. Each variable $x$ is bound to a trace and a position; one step of $t$ advances by one the positions of the variables in $t(0)$ and leaves the others, and $\mathsf{X}$ and $\mathsf{U}$ are evaluated along these steps, with $p_x$ true if $p$ holds at the current position of the trace of $x$. $\mathsf{E}\theta$ holds if $\theta$ holds for some fair trajectory over the quantified variables, starting at position $0$, and $\mathsf{A}\theta$ if it holds for all of them. Trace quantifiers range over a given set of traces. This is the variant of [asynchronous HyperLTL](asynchronous-hyperltl.md) in which trajectories are required to be fair.

**Problem.** The *single-trace satisfiability problem* asks whether a given A-HLTL sentence is satisfied by a set consisting of exactly one trace.

**Theorem (Bozzelli, Peron and Sánchez).** The single-trace satisfiability problem of A-HLTL is $\Sigma^1_1$-hard.

The proof constructs sentences with only two trace variables.

For HyperLTL, single-trace satisfiability coincides with LTL satisfiability and is PSPACE-complete.

## Depends on

- [HyperLTL](../hyperltl.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The reduction is from the recurrence problem for nondeterministic two-counter machines (Harel): does some computation from the initial configuration with zero counters use the designated recurrent transition infinitely often? For a machine $M$ one constructs a two-variable sentence $\varphi_M$ over the propositions $\Delta \cup \{c_1, c_2, \#, \mathit{beg}, \mathit{pad}\}$ that has a single-trace model iff $M$ has a recurrent computation. The key observation is that quantifying twice over the same trace and choosing trajectories enforces alignment requirements between two different stuttering expansions of that trace, which is enough to check that consecutive configurations, written as counter blocks separated by $\#$, are related by the machine's transitions.

## Sources

- L. Bozzelli, A. Peron and C. Sánchez, "Expressiveness and decidability of temporal logics for asynchronous hyperproperties", in *33rd International Conference on Concurrency Theory (CONCUR 2022)*, Leibniz International Proceedings in Informatics 243, Schloss Dagstuhl, 2022, article 27, doi:10.4230/LIPIcs.CONCUR.2022.27; read as arXiv:2207.02956v1, <https://arxiv.org/abs/2207.02956v1>: the section "Results for Asynchronous HyperLTL" (the definition of A-HLTL with fair trajectories, the paragraph "Undecidability of single-trace satisfiability for A-HLTL" and its theorem) and the appendix constructing $\varphi_M$, of arXiv:2207.02956v1.
