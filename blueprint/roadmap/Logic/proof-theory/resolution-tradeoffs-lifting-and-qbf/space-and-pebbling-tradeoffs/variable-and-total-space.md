# Variable space and total space of resolution refutations

Viewing a resolution refutation as a sequence of clause configurations, its variable space is the largest number of distinct variables in a configuration, and its total space is the largest number of literal occurrences, counted with repetitions.

A resolution refutation of a CNF formula $F$ is presented as a sequence of **configurations** $\pi = \{\mathbb{C}_0, \dots, \mathbb{C}_\tau\}$, sets of clauses with $\mathbb{C}_0 = \emptyset$ and $\bot \in \mathbb{C}_\tau$, where each $\mathbb{C}_t$ arises from $\mathbb{C}_{t-1}$ by **axiom download** (add a clause of $F$), **inference** (add a resolvent of two clauses in $\mathbb{C}_{t-1}$) or **erasure** (remove a clause). The **length** is the number of downloads and inferences. For a configuration $\mathbb{C}$:

- the **clause space** is $|\mathbb{C}|$, the number of clauses;
- the **variable space** $\mathit{VarSp}(\mathbb{C})$ is $|\mathrm{Vars}(\mathbb{C})|$, the number of distinct variables mentioned in $\mathbb{C}$;
- the **total space** $\mathit{TotSp}(\mathbb{C})$ is $\sum_{C \in \mathbb{C}} |C|$, the number of literals in $\mathbb{C}$ counted with repetitions.

The space of $\pi$ in each measure is the maximum over its configurations, and the variable space $\mathit{VarSp}(F \vdash \bot)$ and total space $\mathit{TotSp}(F \vdash \bot)$ of refuting $F$ are the minima over all resolution refutations of $F$. Tree-like versions are obtained by requiring that each clause is used at most once before being erased.

## Expansion

Total space is at least variable space, and at least the number of nonempty clauses; it can be smaller than clause space only through the empty clause, since the configuration $\{\bot\}$ has clause space $1$ and total space $0$. For an unsatisfiable CNF in $n$ variables, clause space is at most $n + 1$ (Esteban and Torán), so total space is at most $n(n+1)$, and both bounds are asymptotically attained, for example by random $k$-CNFs. Some papers call total space "variable space"; the terminology here follows Hertel and Urquhart, as adopted in the surveyed papers. Measures are usually studied for $k$-CNF formulas with constant $k$, since width and space can behave artificially for formulas of unbounded width.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a clause](../../../propositional-logic/resolution-size-and-width/width.md)

## Proof depends on

None.

## Sources

- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", *Logical Methods in Computer Science* 9(3:15), 2013, doi:10.2168/LMCS-9(3:15)2013, arXiv:1307.3913v3 (Definitions 2.1, 2.2 and 2.4, Remark 2.5).
- I. Bonacina, "Total space in resolution is at least width squared", *ICALP 2016*, LIPIcs 55, 56:1-56:13, doi:10.4230/LIPIcs.ICALP.2016.56 (Section 1 and the definition of total space in Section 2).
