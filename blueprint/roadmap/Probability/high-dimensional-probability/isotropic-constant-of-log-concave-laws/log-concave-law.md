# Log-concave law

For a positive integer $n$, a log-concave law on $\mathbb{R}^n$ is a
probability measure $\mu$ on $\mathbb{R}^n$ together with a Lebesgue density $f$ of $\mu$ that is
log-concave: $f$ is measurable and nonnegative, and $f((1-t)x + ty) \ge f(x)^{1-t} f(y)^t$ for all
$x, y \in \mathbb{R}^n$ and $0 < t < 1$. Moreover every coordinate $x_i$ and every product
$x_i x_j$ is $\mu$-integrable, and $f \log f$ is Lebesgue integrable.

## Sources

- B. Klartag and J. Lehec, *Affirmative resolution of Bourgain's slicing problem using Guan's bound*, arXiv:2412.15044v1 (2024), Introduction, definition of log-concave functions and measures, and definition (3) of the isotropic constant $L_\mu$; Geom. Funct. Anal. 35 (2025), 1147–1168.
- Catalogue https://github.com/teorth/optimizationproblems, `constants/20b.md`.
