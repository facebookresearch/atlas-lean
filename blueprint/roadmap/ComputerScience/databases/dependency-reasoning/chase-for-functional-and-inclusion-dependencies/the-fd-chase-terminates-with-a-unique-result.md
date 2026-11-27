# The chase for functional dependencies terminates with a unique result

Let $S$ be a finite set of atoms and $\Sigma$ a finite set of functional dependencies, with the
[chase for functional dependencies](the-chase-for-functional-dependencies-on-sets-of-atoms.md). Then there is no infinite
chase sequence of $S$ under $\Sigma$, any two finite chase sequences end in the same result (the symbol $\bot$ or the same set
of atoms), and the chase homomorphisms $h_s, h_{s'}$ of any two successful ones have the same image, $h_s(S) = h_{s'}(S)$. A non-failing step only identifies terms,
so the number of distinct terms decreases at every step.

## Depends on

- [The chase for functional dependencies on sets of atoms](the-chase-for-functional-dependencies-on-sets-of-atoms.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Lemmas 10.6, 10.7 and 10.9 (image equality) (pp. 72–73); proofs deferred there to the chase for equality-generating dependencies.
