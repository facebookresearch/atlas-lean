# The result of the chase for functional dependencies satisfies them

Let $S$ be a finite set of atoms and $\Sigma$ a finite set of functional dependencies. If
$\mathrm{Chase}(S, \Sigma) \ne \bot$, then $\mathrm{Chase}(S, \Sigma)$ satisfies $\Sigma$ (read as a database by treating its
variables as constants).

## Depends on

- [The chase for functional dependencies on sets of atoms](the-chase-for-functional-dependencies-on-sets-of-atoms.md)

## Proof depends on

- [The chase for functional dependencies terminates with a unique result](the-fd-chase-terminates-with-a-unique-result.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Lemma 10.8 (p. 73).
