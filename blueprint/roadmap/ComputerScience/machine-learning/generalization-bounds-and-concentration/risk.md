# Expected risk

Let $\nu$ be a probability distribution on a space $\mathcal{Z}$ of examples $z = (x, y)$, and let $L(f, z)$ be the loss $\ell(y, f(x))$ of a predictor $f$ at the example $z$. The expected risk of $f$ is

$$
R(f) = \mathbb{E}_{z \sim \nu}\big[\ell(y, f(x))\big] = \int L(f, z) \, d\nu(z).
$$

Predictors are abstract: only the loss map $L$ enters.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 2.2, Definition 2.1 (expected risk).
