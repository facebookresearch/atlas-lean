# Raz–Razborov: resolution lower bounds for the weak pigeonhole principle

For every $m > n$, every resolution refutation of the pigeonhole formula $\mathrm{PHP}^{m}_{n}$, asserting an injection from $m$ pigeons into $n$ holes, has size at least

$$
2^{\Omega(n/\log^2 m)}.
$$

For every $m > n$, however large, every resolution refutation of $\mathrm{PHP}^{m}_{n}$ also has size $2^{\Omega(n^{1/3})}$ (Razborov, ECCC TR01-055); in particular even $m = 2^{\sqrt{n}}$ pigeons need refutations of size $2^{\Omega(n^{1/3})}$.

## Proof sketch

Raz proved a $2^{n^{\varepsilon}}$ bound by a pigeon-dance restriction argument showing that every small refutation contains a clause mentioning many holes. Razborov's improvement uses pseudowidth: a refutation is converted into one where every clause is replaced by its ``hole-content'' approximation, and a counting argument over random matchings bounds the number of clauses with large pseudowidth.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Haken's lower bound for the pigeonhole principle](../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Sources

- R. Raz, "Resolution lower bounds for the weak pigeonhole principle", Journal of the ACM 51 (2004) 115-138.
- A. A. Razborov, "Improved resolution lower bounds for the weak pigeonhole principle", ECCC TR01-055; see also A. A. Razborov, "Resolution lower bounds for perfect matching principles", Journal of Computer and System Sciences 69 (2004) 3-27.
