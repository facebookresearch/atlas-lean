# Hall-interval decompositions of ALLDIFFERENT

A decomposition of ALLDIFFERENT into $O(nd^2)$ Boolean interval-membership variables and one cardinality inequality per interval, propagated by ordinary local consistency, enforces range consistency, and a variant enforces bounds consistency, of the original constraint.

Consider $\mathrm{ALLDIFFERENT}(X_1,\dots,X_n)$ (the [constraint](alldifferent-constraint.md) requiring pairwise different values) on $n$ distinct variables with nonempty initial domains contained in $\{1,\dots,d\}$; $n$ is the number of variables and $d$ the length of the value range, not a domain size. An interval $[a,b]$ is a **Hall interval** when exactly $b-a+1$ variables have their domain contained in $[a,b]$, and it is **overloaded** when more than $b-a+1$ do (then the constraint has no solution).

*Range decomposition.* Introduce 0/1 variables $A_{ilu}$ for $1\le i\le n$, $1\le l\le u\le d$, $u-l<n$, and post

$$
A_{ilu}=1 \iff X_i\in[l,u], \qquad \sum_{i=1}^{n}A_{ilu}\le u-l+1 .
$$

*Bounds decomposition.* Add 0/1 variables $B_{ik}$ ($0\le k\le d$, with $B_{i0}=0$ since no value is below 1) and replace the first family by $B_{il}=1\iff X_i\le l$ and $A_{ilu}=1\iff(B_{i(l-1)}=0\wedge B_{iu}=1)$, keeping the inequalities.

**Theorem.** Assume, as the source does for its time bounds, that a constraint of the decomposition is woken only when the domain of one of its variables changes, that propagating a reified constraint costs $O(1)$ per wake-up, and that each inequality is propagated incrementally at $O(n)$ total cost down a branch (bound-change wake-ups for item 2). Costs are totals down one branch of the search tree.

1. Enforcing domain consistency (GAC) on every constraint of the range decomposition, to a common fixpoint, enforces [range consistency](../bounds-and-range-consistency.md) on the ALLDIFFERENT constraint, in $O(nd^3)$ total time down any branch.
2. Enforcing bounds consistency on every constraint of the bounds decomposition enforces [bounds consistency](../bounds-and-range-consistency.md) on the ALLDIFFERENT constraint, in $O(nd^2)$ total time down any branch.

If some interval is overloaded, the inequality for it is violated once its $A_{ilu}$ are forced to 1 and propagation fails; range and bounds consistency are understood with failure when no interval support exists.

## Depends on

- [The ALLDIFFERENT constraint and its value graph](alldifferent-constraint.md): the constraint decomposed.
- [Bounds consistency and range consistency](../bounds-and-range-consistency.md): the consistencies achieved.
- [Generalized arc consistency](../generalized-arc-consistency.md): domain consistency on the constraints of the decomposition.

## Proof depends on

None.

## Expansion

*Item 1.* Leconte's characterization (obligation not expanded here): if no interval is overloaded, ALLDIFFERENT is range consistent iff every Hall interval has been removed from the domains of the variables whose domains are not contained in it. Without the no-overload hypothesis this fails: $D(X_1)=D(X_2)=\{1\}$, $d=1$, has no Hall interval but no solution. Overload is detected by the inequalities, as noted after the theorem. Let $[a,b]$ be a Hall interval with $H=\{i: D(X_i)\subseteq[a,b]\}$, $|H|=b-a+1$. The reified constraints fix $A_{iab}=1$ for $i\in H$, the inequality for $(a,b)$ becomes tight and fixes $A_{iab}=0$ for $i\notin H$, and the reified constraint then removes $[a,b]$ from $D(X_i)$. Cost: $O(nd^2)$ reified constraints, each woken $O(d)$ times at $O(1)$ cost, plus $O(d^2)$ inequalities of cost $O(n)$ down the branch.

*Item 2.* Bounds consistency on a sum of 0/1 variables equals domain consistency; fixing $A_{ilu}=0$ now shrinks a bound of $D(X_i)$ exactly when one bound of the domain meets $[l,u]$, which removes precisely the bounds without bound support. The constraints $B_{il}=1\iff X_i\le l$ occur $O(nd)$ times and are woken $O(d)$ times; the $O(nd^2)$ constraints defining $A_{ilu}$ are woken $O(1)$ times.

The source quotes Leconte's characterization without proof (its pruning half is Lemma 3 of Quimper et al. 2004). The decompositions are propagated by local consistency on Boolean reifications and linear sums, not by unit propagation on clauses.

## Sources

- C. Bessiere, G. Katsirelos, N. Narodytska, C.-G. Quimper and T. Walsh, "Decompositions of all different, global cardinality and related constraints", *Proceedings of the Twenty-First International Joint Conference on Artificial Intelligence (IJCAI 2009)*, 419–423, [https://www.ijcai.org/proceedings/2009/77](https://www.ijcai.org/proceedings/2009/77). Hall intervals, the decompositions (1)–(4), Theorem 1 (range consistency) and Theorem 2 (bounds consistency) with proofs, §3 of arXiv:0905.3755v1, [https://arxiv.org/abs/0905.3755v1](https://arxiv.org/abs/0905.3755v1).
- M. Leconte, "A bounds-based reduction scheme for constraints of difference", *Constraint-96 International Workshop on Constraint-Based Reasoning* (1996), 19–28, cited by the source for the range consistency characterization (reference as given by Quimper, López-Ortiz, van Beek and Golynski, CP 2004, whose Lemma 3 restates the pruning rule).
