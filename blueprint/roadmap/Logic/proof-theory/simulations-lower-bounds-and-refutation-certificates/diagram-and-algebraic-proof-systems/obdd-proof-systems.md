# OBDD-based proof systems with join, weakening and reordering

An OBDD proof refutes a CNF formula by a sequence of ordered binary decision diagrams that starts from the clauses and ends with the constant false, using conjunction of two diagrams in the same variable order, semantic weakening, and optionally reordering a diagram into another variable order.

Let $\Gamma = \{x_1, \dots, x_n\}$ and let $\pi$ be a permutation of $[n]$. A **$\pi$-OBDD** is a binary decision diagram (a dag with one source, sinks labelled $0$ or $1$, every other vertex labelled by a variable and having one outgoing edge labelled $0$ and one labelled $1$) such that on every source-to-sink path each variable occurs at most once and $x_{\pi(i)}$ never appears before $x_{\pi(j)}$ when $i > j$. Every OBDD comes with a fixed order $\pi$, even if it does not query all variables. Its size is its number of vertices.

Let $\varphi$ be an unsatisfiable CNF formula. An **OBDD proof** of $\varphi$ is a sequence $D_1, \dots, D_t$ of OBDDs with orders $\pi_1, \dots, \pi_t$ such that $D_t$ is a $\pi_t$-OBDD representing the constant false function and each $D_i$ either is a $\pi_i$-OBDD representing a clause of $\varphi$ or follows from earlier lines by one of the rules:

- **Join** ($\wedge$): $D_i$ represents $D_k \wedge D_\ell$ for some $k, \ell < i$ with $\pi_i = \pi_k = \pi_\ell$;
- **Weakening**: for some $j < i$ with $\pi_i = \pi_j$, every assignment satisfying $D_j$ satisfies $D_i$;
- **Reordering**: $D_i$ is a $\pi_i$-OBDD equivalent to a $\pi_j$-OBDD $D_j$ for some $j < i$.

The size of the proof is $\sum_{i=1}^{t} |D_i|$. The system $\mathrm{OBDD}(\wedge)$ allows only join; $\mathrm{OBDD}(\wedge, \mathrm{weakening})$ allows join and weakening, so all its lines share one order $\pi$ and one speaks of $\pi$-$\mathrm{OBDD}(\wedge, \mathrm{weakening})$ proofs; $\mathrm{OBDD}(\wedge, \mathrm{reordering})$ and $\mathrm{OBDD}(\wedge, \mathrm{weakening}, \mathrm{reordering})$ add reordering. A proof is **tree-like** if every line is used as a premise at most once.

## Expansion

Each system is a Cook-Reckhow proof system: for a fixed order there is a unique minimal $\pi$-OBDD of every function, conjunction, negation and satisfiability testing of $\pi$-OBDDs run in polynomial time, so a weakening step $D_j \models D_i$ is checked by testing $D_j \wedge \neg D_i$ for unsatisfiability, and a reordering step is checked with the algorithm that converts a $\pi$-OBDD to the minimal $\rho$-OBDD in time polynomial in input plus output size. $\mathrm{OBDD}(\wedge, \mathrm{weakening})$ was introduced by Atserias, Kolaitis and Vardi, who showed it simulates Cutting Planes with unary coefficients; the reordering rule was introduced by Itsykson et al., with joins still restricted to diagrams of the same order.

## Depends on

- [Binary decision diagram](../../../propositional-logic/binary-decision-diagrams/reduced-ordered-binary-decision-diagrams-canonic/bdd.md)
- [Cook-Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss, Dmitry Itsykson, Alexander Knop, Dmitry Sokolov, "Reordering Rule Makes OBDD Proof Systems Stronger", *33rd Computational Complexity Conference (CCC 2018)*, LIPIcs, 2018, doi:10.4230/LIPIcs.CCC.2018.16 (Section 2.1 for $\pi$-OBDDs; Section 2.2.3 for OBDD proofs, the three rules, size and tree-likeness).
