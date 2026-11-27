# The chase for inclusion dependencies has a unique result

Let $S$ be a finite set of atoms and $\Sigma$ a finite set of inclusion dependencies, with the
[chase for inclusion dependencies](the-chase-for-inclusion-dependencies.md). Then:

1. there is a finite chase sequence of $S$ under $\Sigma$ if and only if there is no infinite one;
2. any two finite chase sequences have the same result; and
3. any two infinite chase sequences have the same result.

The fixed naming of new variables makes the atom added for a given dependency and tuple independent of when it is added;
the result is the least set of atoms that contains $S$ and contains $\mathrm{new}(\sigma, \bar u)$ whenever it contains
$R(\bar u)$ for $\sigma = R[\alpha] \subseteq P[\beta]$ in $\Sigma$, that is, the least fixpoint of
$X \mapsto S \cup X \cup \{\mathrm{new}(\sigma, \bar u) : \sigma \in \Sigma,\ R(\bar u) \in X\}$.

## Depends on

- [The chase for inclusion dependencies](the-chase-for-inclusion-dependencies.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Lemma 11.6 and the preceding discussion (pp. 80–81); proofs deferred there to the chase for tuple-generating dependencies.
