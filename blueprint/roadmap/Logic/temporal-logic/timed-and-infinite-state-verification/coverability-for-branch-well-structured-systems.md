# Coverability is undecidable for branch-well-structured transition systems

Relaxing the well-quasi-order and monotony conditions of well-structured transition systems along single branches keeps non-termination decidable, but coverability becomes undecidable even for strongly monotone systems over a well-quasi-order with computable successors, and boundedness is undecidable without strict monotony.

**Branch-WSTS.** An *ordered labeled transition system* $\mathcal S=(X,\Sigma,\to,\le,x_0)$ has a set $X$ of states, labeled transitions, a quasi-order $\le$ on $X$ and an initial state $x_0$. It is *branch-wqo* if, along every run from $x_0$, the set of visited states is finite or well-quasi-ordered by $\le$, and *branch-monotone* if whenever $x\xrightarrow{\sigma}x'$ with $x\le x'$ there is $y$ with $x'\xrightarrow{\sigma}y$ and $x'\le y$. A *branch-WSTS* is a finitely branching, branch-monotone, branch-wqo system; every [well-structured transition system](well-structured-transition-systems.md) with strong monotony is one. It is *branch-effective* if $\le$ and $\to$ are decidable and the finite set of successors of each state is computable. The *coverability problem* asks, given states $x_0$ and $y$, whether some state $x$ reachable from $x_0$ satisfies $y\le x$; the *boundedness problem* asks whether the set of states reachable from $x_0$ is finite.

**Theorem (Bollig, Finkel and Suresh).**

1. Coverability is undecidable for branch-effective branch-WSTS, even if the system is strongly monotone and $\le$ is a well-quasi-order.
2. Boundedness is undecidable for branch-effective branch-WSTS in which $\le$ is a well-quasi-order.
3. Coverability is undecidable for cover-WSTS, the finitely branching systems over a well-quasi-order that are cover-monotone (monotone only with respect to states below the downward closure of the reachable states).

By contrast, non-termination is decidable for branch-effective branch-WSTS, and boundedness is decidable for those with strict branch-monotony and a partial order; coverability is decidable for cover-WSTS with additional effectiveness assumptions. For well-structured transition systems with an effective predecessor basis, [coverability is decidable](coverability-is-decidable-for-well-structured.md); part 1 shows that computable successors alone do not suffice.

## Depends on

- [Well-structured transition systems](well-structured-transition-systems.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Part 1 uses a family of systems from earlier work on well-structured transition systems, on $\mathbb N^2$ ordered componentwise: for the $j$-th Turing machine, a computable function $f_j$, defined from the behavior of that machine, and the function $g(n,k)=(n+1,k)$ induce a strongly monotone, branch-effective system in which $(1,1)$ is coverable from $(0,0)$ exactly when the $j$-th machine halts. Part 2 follows because reset Petri nets are effective WSTS with general monotony whose boundedness problem is undecidable (Dufourd, Finkel and Schnoebelen). Part 3 simulates counter machines by cover-WSTS. A good expansion links pages for the undecidability of boundedness of reset Petri nets and for this family of systems; neither has a page yet.

## Sources

- B. Bollig, A. Finkel and A. Suresh, "Branch-well-structured transition systems and extensions", *Logical Methods in Computer Science* 20(2), paper 12, 2024, doi:[10.46298/lmcs-20(2:12)2024](https://doi.org/10.46298/lmcs-20(2:12)2024); read in arXiv:2211.15913v4 ([arXiv](https://arxiv.org/abs/2211.15913v4)): the definitions of branch-wqo, branch-monotony, branch-WSTS and branch-effectiveness, the decidability theorems for non-termination and boundedness, the undecidability proposition for boundedness, the undecidability theorem for coverability of branch-WSTS with its proof, and the definition of cover-WSTS with the undecidability theorem for their coverability.
