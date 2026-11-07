# Bochner's theorem

Let $f : \mathbb{R} \to \mathbb{C}$. Then $f$ is continuous, satisfies
$f(0) = 1$, and is positive definite, meaning that for every $n \in \mathbb{N}$, all points
$x_1, \dots, x_n \in \mathbb{R}$ and all coefficients $c_1, \dots, c_n \in \mathbb{C}$ the sum
$S = \sum_{i=1}^{n} \sum_{j=1}^{n} \overline{c_i}\, c_j\, f(x_i - x_j)$ is a nonnegative real
number, if and only if there is a Borel probability measure $\mu$ on $\mathbb{R}$ such that
$f(t) = \int_{\mathbb{R}} e^{itx} \, d\mu(x)$ for every $t \in \mathbb{R}$, that is, $f$ is the
characteristic function of $\mu$.

## Sources

- Bochner's theorem on positive-definite functions, S. Bochner, Vorlesungen über Fouriersche Integrale 1932 and Math. Ann. 108 (1933); see Folland, Abstract Harmonic Analysis, Fourier Analysis on Groups; Lean is ℝ→ℂ iff version continuous f 0=1 positive- definite via double sum iff ∃ Borel probability μ with f = charFun μ, fixed +I sign via charFun.
