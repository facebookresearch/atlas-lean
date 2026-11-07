# Fourier decay of a circle measure passes to integrable densities

Let $\mu$ be a finite
Borel measure on $\mathbb{C}$ concentrated on the unit circle $T = \{z \in \mathbb{C} : |z| = 1\}$,
that is, $\mu$-almost every $z$ lies in $T$, and suppose that $\int z^n \, d\mu(z) \to 0$ as
$n \to \infty$ through $\mathbb{N}$. Then for every $\mu$-integrable function
$f : \mathbb{C} \to \mathbb{C}$,

$$
\lim_{n \to \infty} \int z^n f(z) \, d\mu(z) = 0.
$$

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Set functions and measures on spaces with additional structure), `benchmark/level2/ma_proofbench_l2_13.lean` at openbmb/ma-proofbench@31bab4c.
