# The chase for functional dependencies runs in polynomial time

Given a finite set of atoms $S$ and a finite set $\Sigma$ of functional dependencies, $\mathrm{Chase}(S, \Sigma)$ can be computed in
time polynomial in the sizes of $S$ and $\Sigma$, and when it is not $\bot$ so can the chase homomorphism of a successful sequence, with terms compared by the fixed
polynomial-time order.

## Depends on

- [The chase for functional dependencies on sets of atoms](the-chase-for-functional-dependencies-on-sets-of-atoms.md)
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [The chase for functional dependencies terminates with a unique result](the-fd-chase-terminates-with-a-unique-result.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Lemma 10.10 (p. 73).
