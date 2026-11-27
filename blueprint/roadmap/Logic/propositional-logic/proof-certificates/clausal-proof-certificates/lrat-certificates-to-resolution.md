# RUP steps and resolution steps simulate each other

Let $\Gamma$ be a set of clauses and $n$ the total number of literal occurrences in the clauses of $\Gamma$. If a clause $C$ is derivable from $\Gamma$ by a single resolution inference, then $C$ is a reverse unit propagation (RUP) clause with respect to $\Gamma$: unit propagation refutes $\Gamma$ together with the negations of the literals of $C$. Conversely, if $C$ is a RUP clause with respect to $\Gamma$, then some subclause $C' \subseteq C$ has a resolution derivation from $\Gamma$ of length at most $n$. In particular, each RUP addition step of an LRAT certificate, whose clause is RUP with respect to the clause database at that step, is matched by a short resolution derivation of a subclause of the added clause, and each resolution step can be logged as a RUP addition step.

## Proof sketch

For a resolvent $C = D \vee E$ of $p \vee D$ and $\neg p \vee E$, falsifying $C$ makes the two premises unit on $p$ and $\neg p$, a conflict. Conversely, a unit propagation refutation of $\Gamma$ together with the negated literals of $C$ has length at most $n$; removing the resolutions against the unit clauses for the literals of $C$ turns it into a resolution derivation of $C$ or of a subclause of $C$ from $\Gamma$. (Derived, not stated by the sources: replacing each added clause by the derived subclause keeps every later RUP step valid, so an accepted certificate for a CNF formula $\varphi$ consisting of RUP addition steps and deletions yields a resolution refutation of $\varphi$; each RUP step with hints $h_1, \dots, h_k$ is a trivial resolution chain of at most $\min(k, N)$ resolutions, $N$ the number of variables, giving at most $|\varphi| + \min(H, S \cdot N)$ lines for $H$ hints and $S$ steps in total; conversely a tree-like resolution refutation with $s$ nodes compiles into an accepted LRAT certificate with one RUP step per resolution step, each hinting its two premises.)

## Depends on

- [Accepted LRAT proofs refute CNF formulas](../accepted-lrat-proofs-refute-cnf-formulas.md)
- [Resolution refutation](../../resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Trivial resolution derivations](trivial-resolution-derivations.md)

## Sources

- S. Buss and N. Thapen, "DRAT and Propagation Redundancy Proofs Without New Variables", Logical Methods in Computer Science 17(2), 2021; arXiv:1909.00520: Definition 1.2 and Lemma 1.4.
- P. Beame, H. Kautz and A. Sabharwal, "Towards Understanding and Harnessing the Potential of Clause Learning", Journal of Artificial Intelligence Research 22, 319–351, 2004: Proposition 3 (a trivial resolution derivation of $C$ gives a unit propagation conflict after falsifying $C$).
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
