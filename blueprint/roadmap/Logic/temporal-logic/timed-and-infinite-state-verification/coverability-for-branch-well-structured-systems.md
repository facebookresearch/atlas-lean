# Coverability is undecidable for branch-well-structured transition systems

Relaxing the well-quasi-order and monotony conditions of well-structured transition systems along single branches keeps non-termination decidable, but coverability becomes undecidable even for strongly monotone systems over a well-quasi-order with computable successors, and boundedness is undecidable without strict monotony.

**Branch-WSTS.** An *ordered labeled transition system* $\mathcal S=(X,\Sigma,\to,\le,x_0)$ has a set $X$ of states, labeled transitions, a quasi-order $\le$ on $X$ and an initial state $x_0$. It is *branch-wqo* if, along every run from $x_0$, the set of visited states is finite or well-quasi-ordered by $\le$, and *branch-monotone* if for all states $x, x'$ and all label words $\sigma\in\Sigma^*$, whenever $x\xrightarrow{\sigma}x'$ (a run reading $\sigma$) with $x\le x'$, there is $y$ with $x'\xrightarrow{\sigma}y$ and $x'\le y$ (Definition 3.5). A *branch-WSTS* is a finitely branching, branch-monotone, branch-wqo system; every finitely branching [well-structured transition system](well-structured-transition-systems.md) with strong monotony is one (Definition 3.8). It is *branch-effective* if $\le$ and $\to$ are decidable and the finite set of successors of each state is computable. For a system with initial state $x_0$, the *coverability problem* ($x_0$-coverability) asks, given a state $y$, whether some state $x$ reachable from $x_0$ satisfies $y\le x$ (Definitions 2.5 and 5.8); the *boundedness problem* asks whether the set of states reachable from $x_0$ is finite.

**Theorem (Bollig, Finkel and Suresh).** Coverability is undecidable for branch-effective branch-WSTS, even if the system is strongly monotone and $\le$ is a well-quasi-order (Theorem 5.2 of the source). Instances are given effectively, by programs for the successor function and for $\le$; the proof uses the systems $S_j$ on $\mathbb N^2$ with the componentwise order and the two computable successor functions $g(n, k) = (n + 1, k)$ and $f_j$, where $f_j(n, 0) = (n, 0)$ if the $j$-th Turing machine runs for more than $n$ steps and $f_j(n, k) = (n, n + k)$ otherwise, and $(1, 1)$ is coverable from $(0, 0)$ in $S_j$ exactly when that machine halts.

The source also shows that boundedness is undecidable for branch-effective branch-WSTS in which $\le$ is a well-quasi-order (Proposition 3.16), and that coverability from a given starting state is undecidable for cover-WSTS, the finitely branching systems over a well-quasi-order that are cover-monotone: for every state $y_1$ in $\mathrm{Cover}(x_0) = {\downarrow}\mathrm{Post}^*(x_0)$ and all states $x_1 \le y_1$ and $x_1 \to x_2$, there is $y_2$ with $y_1 \to^* y_2$ and $x_2 \le y_2$ (Definition 5.3). In that result the starting state is part of the input and may differ from the distinguished $x_0$ from which cover-monotony is promised: the proof of Theorem 5.10 makes the distinguished state a new sink, which makes cover-monotony vacuous, and asks coverability of a counter machine from its own initial state.

By contrast, non-termination is decidable for branch-effective branch-WSTS (Theorem 3.15), and boundedness is decidable for those with strict branch-monotony and a partial order (Theorem 3.13); $x_0$-coverability, from the distinguished initial state, is decidable for ideally effective cover-WSTS with computable successors (Theorem 5.9). For well-structured transition systems with an effective predecessor basis, [coverability is decidable](coverability-is-decidable-for-well-structured.md); the theorem shows that computable successors alone do not suffice.

## Depends on

- [Well-structured transition systems](well-structured-transition-systems.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The theorem uses a family of systems from earlier work on well-structured transition systems, on $\mathbb N^2$ ordered componentwise: for the $j$-th Turing machine, a computable function $f_j$, defined from the behavior of that machine, and the function $g(n,k)=(n+1,k)$ induce a strongly monotone, branch-effective system in which $(1,1)$ is coverable from $(0,0)$ exactly when the $j$-th machine halts. The boundedness result (Proposition 3.16) follows because reset Petri nets are effective WSTS with general monotony whose boundedness problem is undecidable (Dufourd, Finkel and Schnoebelen). Theorem 5.10 simulates counter machines by cover-WSTS. A good expansion links pages for the undecidability of boundedness of reset Petri nets and for this family of systems.

## Sources

- B. Bollig, A. Finkel and A. Suresh, "Branch-well-structured transition systems and extensions", *Logical Methods in Computer Science* 20(2), paper 12, 2024, doi:[10.46298/lmcs-20(2:12)2024](https://doi.org/10.46298/lmcs-20(2:12)2024); read in arXiv:2211.15913v4 ([arXiv](https://arxiv.org/abs/2211.15913v4)): Definitions 3.1, 3.5, 3.8 and 3.12 (branch-wqo, branch-monotony, branch-WSTS and branch-effectiveness), Theorems 3.13 and 3.15 (boundedness and non-termination), Proposition 3.16, Definition 2.5 (coverability from the initial state), Theorem 5.2 with its proof, Definition 5.3 (cover-monotony), Definition 5.8 ($x_0$-coverability), and Definition 5.6 (cover-WSTS) with Theorems 5.9 and 5.10.
