# Datalog programs and the immediate consequence operator

A Datalog program is a finite set of function-free Horn rules over extensional (EDB) and intensional
(IDB) predicates, each rule safe: every variable of its head occurs in its body. For a finite EDB instance
$I$, let $U$ be the finite set consisting of the active domain of $I$ and the constants of $P$. The
immediate-consequence operator $T_{P,I}$ maps an IDB instance $J$ over $U$ to the set of IDB facts that are
heads of ground rule instances over $U$ whose bodies hold in $I \cup J$. Monotonicity of $T_{P,I}$ on the
finite lattice of IDB instances over $U$ is a separate lemma.

## Expansion

This node states a precise definition. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: conjunctive queries, answers and canonical databases (for rule bodies and their satisfaction).

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice). Sections 12.1 (syntax of datalog) and 12.3 (fixpoint semantics, immediate consequence operator). <http://webdam.inria.fr/Alice/pdfs/all.pdf>
- Database Theory (SS2025), TU Dresden ICCL — TU Dresden, International Center for Computational Logic. <https://iccl.inf.tu-dresden.de/web/Database_Theory_(SS2025)> Background reference.
