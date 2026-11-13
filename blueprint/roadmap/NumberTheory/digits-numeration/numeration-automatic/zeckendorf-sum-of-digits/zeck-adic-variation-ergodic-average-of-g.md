# Ergodic averages of the variation for functions of polynomial growth

Let $\mathbb{X}$ be
the set of Zeckendorf-adic integers, $T$ the Zeckendorf odometer, and $\mathbb{P}$ a
$T$-invariant probability measure on binary sequences with $\mathbb{P}(\mathbb{X}^c) = 0$. Let
$s(n)$ be the number of terms in the Zeckendorf representation of $n \in \mathbb{N}$, let
$r \ge 1$, and let $\Delta^{(r)}$ and $\Delta_k^{(r)}$ be the variation and the truncated
variation on binary sequences. Let $f : \mathbb{Z} \to \mathbb{C}$ and let $\alpha \ge 1$ and
$C > 0$ be reals with $|f(n)| \le C|n|^\alpha + |f(0)|$ for all $n \in \mathbb{Z}$. Then
$f \circ \Delta^{(r)}$ is $\mathbb{P}$-integrable,

$$\frac{1}{N} \sum_{n=0}^{N-1} f\bigl(s(n + r) - s(n)\bigr)
\to \int f \circ \Delta^{(r)}\,d\mathbb{P}$$

as $N \to \infty$, and
$\int f \circ \Delta_k^{(r)}\,d\mathbb{P} \to \int f \circ \Delta^{(r)}\,d\mathbb{P}$
as $k \to \infty$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Proposition 23 (`jis-2024-24.3.2-prop-23`).
