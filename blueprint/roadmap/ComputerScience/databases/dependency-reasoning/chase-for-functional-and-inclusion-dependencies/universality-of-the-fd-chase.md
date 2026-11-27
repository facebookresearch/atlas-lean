# Universality of the chase for functional dependencies

Let $S$ be a finite set of atoms, $\Sigma$ a finite set of functional dependencies with $\mathrm{Chase}(S, \Sigma) \ne \bot$, and
$S'$ a set of atoms that satisfies $\Sigma$. If $(S, \bar u) \to (S', \bar v)$ for tuples $\bar u, \bar v$, then

$$\bigl(\mathrm{Chase}(S, \Sigma), h_{S, \Sigma}(\bar u)\bigr) \to (S', \bar v).$$

So the chase result maps homomorphically to every set of atoms that satisfies $\Sigma$ and receives a homomorphism from
$S$. The tableau version for functional and join dependencies is the [tableau chase](../../dependencies-and-the-chase/chasing-tableau-queries-with-functional-and-join-dependencie.md).

## Depends on

- [The chase for functional dependencies on sets of atoms](the-chase-for-functional-dependencies-on-sets-of-atoms.md)
- [Containment, equivalence and homomorphisms of conjunctive queries](../../conjunctive-queries/cores-and-minimization/containment-equivalence-and-homomorphisms-of-conjunctive-queries.md)
- [A functional dependency holds in a relation](../../functional-dependencies/holds-in.md)

## Proof depends on

- [The chase for functional dependencies terminates with a unique result](the-fd-chase-terminates-with-a-unique-result.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Lemma 10.11 (p. 74), and its use in Proposition 10.13 (p. 75).
