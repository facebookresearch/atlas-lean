# RUP clauses have short resolution derivations

If a CNF formula $F$ implies a non-tautological clause $C$ via unit propagation using $n$ propagation steps (so $C$ is a [RUP](../proof-certificates/rup-and-rat-clauses.md) in $F$), then $C$ can be derived from $F$ by at most $n$ resolution steps followed by one subsumed-clause addition: the derived clause $C_1$ subsumes $C$.

## Depends on

- [RUP and RAT clauses](../proof-certificates/rup-and-rat-clauses.md)
- [Resolution derivability](../resolution/resolution-derivable.md)

## Sources

- B. Kiesl, A. Rebola-Pardo, M. J. H. Heule and A. Biere, "Simulating strong practical proof systems with extended resolution", *Journal of Automated Reasoning* 64:1247–1267, 2020, <https://cca.informatik.uni-freiburg.de/papers/KieslRebolaPardoHeuleBiere-JAR20.pdf>, Section 4.3: Algorithm 1, Lemma 1 (the clause $C_1$ subsumes $C$) and Theorem 2.
