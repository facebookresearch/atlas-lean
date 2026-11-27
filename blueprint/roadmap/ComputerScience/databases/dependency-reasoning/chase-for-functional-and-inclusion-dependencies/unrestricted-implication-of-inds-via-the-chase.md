# Unrestricted implication of inclusion dependencies via the chase

Fix a countably infinite value domain, and write $\Sigma \models_\infty \sigma$ when a set $\Sigma$ of inclusion dependencies
implies an inclusion dependency $\sigma$ [without restriction](../../dependencies-and-the-chase/implies.md) over it, that is, over all instances, whose
relations may be infinite. The domain matters: over a one-element domain every inclusion dependency between nonempty
relations holds, and the chase test below fails to characterize implication. For $\sigma = R[i_1, \dots, i_k] \subseteq P[j_1, \dots, j_k]$
let $S_\sigma = \{R(x_1, \dots, x_{\mathrm{ar}(R)})\}$ with distinct variables. Then

$$\Sigma \models_\infty \sigma \iff \mathrm{Chase}(S_\sigma, \Sigma) \models \sigma .$$

Since finite and unrestricted implication coincide for inclusion dependencies, the same test decides finite implication.

## Depends on

- [The chase for inclusion dependencies](the-chase-for-inclusion-dependencies.md)
- [Unrestricted implication of dependencies](../../dependencies-and-the-chase/implies.md)

## Proof depends on

- [The result of the chase for inclusion dependencies satisfies them](the-result-of-the-ind-chase-satisfies-the-dependencies.md)
- [Universality of the chase for inclusion dependencies](universality-of-the-ind-chase.md)
- [Finite and unrestricted implication of functional and inclusion dependencies](../../dependencies-and-the-chase/finite-and-unrestricted-implication-of-functional-and-inclusion.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Lemma 11.10, Theorem 11.11 and Corollary 11.12 (pp. 82–83).
