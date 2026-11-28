# Converse for lossy source coding

Let $X_1, X_2, \dots$ be independent with common distribution $P_X$ on a finite alphabet, with a bounded
distortion measure $d$ on a finite reconstruction alphabet, and let

$$R(D) = \inf\{ I(X;\hat{X}) : P_{\hat{X}\mid X} \text{ with } \mathbb{E}\, d(X,\hat{X}) \le D \} \in [0, +\infty],$$

with $\inf \emptyset = +\infty$.
Then $R$ is convex and nonincreasing in $D$, and every block code with expected per-letter distortion at most
$D$ has rate at least $R(D)$.

## Depends on

- [Mutual information of a finite joint law](../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)

## Proof depends on

- [Data-processing inequality](../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information-le-left-of-mar.md)

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025 (author draft), Theorem 24.3 (general converse), Corollary 24.6, Theorem 24.7 and Theorem 24.8. <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
