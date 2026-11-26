# Extended resolution polynomially simulates DRAT

There is a polynomial-time transformation of every [DRAT proof](drat-proofs.md) of a formula $F$ into an [extended-resolution proof](extended-resolution.md) of $F$; a DRAT proof of size $P$ yields one of size $O(P^4)$. So extended resolution and DRAT are polynomially equivalent, every extended-resolution proof being a DRAT proof.

**Proof outline.** An extended-resolution proof is a DRAT proof: a resolvent is a RUP, and the clauses of a definition with a fresh variable $x$ can be added in the order $x \vee \bar p$, $x \vee \bar c_1 \vee \dots \vee \bar c_k$, $\bar x \vee p \vee c_j$, the first two as RATs on $x$ with no clause containing $\bar x$ to check, the others as RATs on $\bar x$, whose resolvents with the first two clauses are tautologies. Conversely, each addition of a RAT that is not a RUP is replaced by one definition introduction followed by RUP additions and clause deletions; deletions are then dropped; each RUP addition is replaced by [resolution steps and a subsumed-clause addition](rup-clauses-have-short-resolution-derivations.md); and subsumed-clause additions are eliminated by relabelling the resulting derivation.

## Depends on

- [DRAT proofs](drat-proofs.md)
- [Extended resolution](extended-resolution.md)

## Proof depends on

- [RUP clauses have short resolution derivations](rup-clauses-have-short-resolution-derivations.md)

## Sources

- B. Kiesl, A. Rebola-Pardo, M. J. H. Heule and A. Biere, "Simulating strong practical proof systems with extended resolution", *Journal of Automated Reasoning* 64:1247–1267, 2020, <https://cca.informatik.uni-freiburg.de/papers/KieslRebolaPardoHeuleBiere-JAR20.pdf>, the abstract and Section 4 (the four-stage simulation, Sections 4.1–4.4, and the size analysis giving $O(P^4)$).
