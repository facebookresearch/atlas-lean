# LRAT addition steps certify RUP and RAT clauses

Use the notions of [RUP and RAT clauses](rup-and-rat-clauses.md). An LRAT proof acts on a formula given as a finite map from clause
identifiers to clauses. A deletion step removes the listed identifiers. An addition step for a new clause $C_j$ lists positive hints
$i'_1, \dots, i'_r$, then groups $(-i_k, \mathit{hints}_k)$ for $k = 1, \dots, n$. The checker works on a growing list $C$ of literals, initially $C_j$:

1. For each positive hint $i'$ in turn it computes $C_{i'} \setminus C$. If this is empty, it accepts the step: $C_j$ is AT. If it has two or more
   literals, it rejects. If it is a single literal $m$, it appends $\bar m$ to $C$.
2. Otherwise it rejects if $C_j$ is empty and takes as pivot $p$ the first literal of $C$, which is the first literal of $C_j$. For every
   clause $C_i$ of the formula containing $\bar p$, it skips $C_i$ if $C_i$ and $C$ share a complementary pair other than $p, \bar p$. Otherwise
   it requires a group with $i_k = i$ and runs step 1 on $C \cup (C_i \setminus \{\bar p\})$ with $\mathit{hints}_k$, which must reach an empty
   clause.

**Theorem.** If a deletion step or an accepted addition step turns the formula $F$ into $F'$, then $F'$ is satisfiable whenever $F$ is. An
addition accepted in step 1 makes $C_j$ AT with respect to $F$, so $F \models C_j$ and $F \cup \{C_j\}$ is logically equivalent to $F$. An
addition accepted in step 2 makes $C_j$ RAT on $p$ with respect to $F$, so $F \cup \{C_j\}$ is satisfiability-equivalent to $F$, though in
general not logically equivalent. The end-to-end consequence for a whole proof is [accepted LRAT proofs refute CNF formulas](accepted-lrat-proofs-refute-cnf-formulas.md).

For RAT: if $\tau$ satisfies $F$ but falsifies $C_j$, every resolvent on $p$ is satisfied by $\tau$, so each clause of $F$ containing $\bar p$ has
another literal true under $\tau$, and flipping $p$ to true satisfies both $F$ and $C_j$.

## Depends on

- [RUP and RAT clauses](rup-and-rat-clauses.md)

## Proof depends on

- [RUP and RAT clauses](rup-and-rat-clauses.md)

## Sources

- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient certified RAT verification", *CADE 2017*, LNCS 10395, Springer, 2017, <http://www.cs.cmu.edu/~mheule/publications/lrat.pdf>: Section 2 (deletion steps preserve satisfiability), Section 3 (LRAT lines and hints, Figure 3) and Section 4 (algorithm check_RAT and the statement that an accepted proof preserves satisfiability).
- M. Järvisalo, M. J. H. Heule and A. Biere, "Inprocessing rules", *IJCAR 2012*, LNCS 7364, Springer, 2012, <http://fmv.jku.at/papers/JarvisaloHeuleBiere-IJCAR12.pdf>: Proposition 1 (adding a RAT clause preserves satisfiability) and Figure 2 (AT preserves logical equivalence, RAT does not).
