# Lévy–Khintchin representation on the real line

A probability measure $\mu$ on
$\mathbb{R}$ is infinitely divisible, meaning that for every integer $n \ge 1$ there is a
probability measure $\rho$ on $\mathbb{R}$ whose $n$-fold convolution power $\rho^{\ast n}$
equals $\mu$, if and only if there are real numbers $\gamma$ and $\sigma \ge 0$ and a measure
$\nu$ on $\mathbb{R}$ with $\nu(\{0\}) = 0$ and
$\int \min(1, x^2)\, d\nu(x) < \infty$ such that the characteristic function $\hat\mu$ of $\mu$
satisfies, for every $t \in \mathbb{R}$,

$$
\hat\mu(t) = \exp\Big(i \gamma t - \frac{\sigma^2 t^2}{2} +
\int_{\mathbb{R}} \big(e^{itx} - 1 - itx \, \mathbf{1}_{\{|x| \le 1\}}(x)\big) \, d\nu(x)\Big).
$$

Proof: The reverse implication uses compound Poisson approximation plus Lévy continuity; the
forward implication uses a distinguished logarithm, canonical measures, and Prokhorov compactness.
For the equivalence, see William Feller, *An Introduction to Probability Theory and Its
Applications*, vol. II, Theorem XVII.2.1.

## Sources

- Ken-iti Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge Studies in Advanced Mathematics 68, Cambridge University Press (1999), Theorem 8.1, pp. 37–38, ISBN 978-0-521-55302-5. <https://books.google.com/books?vid=ISBN9780521553025&jscmd=SearchWithinVolume2&q=Theorem+8.1> Scope: restricts Sato Theorem 8.1 (stated for `ℝ^d`) to `ℝ`, and formalizes only the existence direction (i), omitting uniqueness of the generating triplet (ii). The jump integrand uses the hard truncation `x * 1_{|x| ≤ 1}`, which is an equivalent convention to Sato's `x / (1 + |x|^2)` after reparameterizing the drift `γ`.
