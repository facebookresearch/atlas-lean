# Minimizations and cores of unions of conjunctive queries

Let $q = q_1 \cup \dots \cup q_n$ be a [union of conjunctive queries](containment-of-unions-of-conjunctive-queries.md) over a
schema $\mathbf S$ with head tuple $\bar x$.

- A UCQ $q' = q'_1 \cup \dots \cup q'_m$ over $\mathbf S$ with $m \le n$ is a *minimization* of $q$ when $q' \equiv q$, every
  conjunctive query $p$ over $\mathbf S$ with $p \equiv q'_i$ has at least as many body atoms as $q'_i$ (for each $i$), and
  every UCQ equivalent to $q'$ has at least $m$ disjuncts.
- A UCQ $q'(\bar x) = q'_1 \cup \dots \cup q'_m$ is a *core* of $q$ when (1) $m \le n$ and there are distinct indices
  $i_1, \dots, i_m \in [n]$ such that each $q'_j$ is a [core](minimizations-and-cores-of-conjunctive-queries.md) of $q_{i_j}$;
  (2) for every $i \in [n]$ there is $j \in [m]$ with $q_i \subseteq q'_j$; and (3) for every $i \in [m]$ there is no
  $j \in [m] \setminus \{i\}$ with $q'_i \subseteq q'_j$.
- Two UCQs $q_1 \cup \dots \cup q_n$ and $q'_1 \cup \dots \cup q'_m$ are isomorphic when $n = m$ and some bijection $\pi$ of
  their disjuncts makes $q_i$ and $\pi(q_i)$ isomorphic conjunctive queries for every $i$.

## Depends on

- [Containment of unions of conjunctive queries](containment-of-unions-of-conjunctive-queries.md)
- [Minimizations and cores of conjunctive queries](minimizations-and-cores-of-conjunctive-queries.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 29.8 and 29.9 (pp. 265–266) and the definition of isomorphic UCQs before Proposition 29.12 (p. 268).
