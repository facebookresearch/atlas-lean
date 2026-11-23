# Salem–Zygmund central limit theorem for lacunary sine sums

Let $(r_k)_{k \ge 0}$ be a sequence of positive integers with Hadamard gaps: there is $q > 1$ such
that $r_{k+1} / r_k \ge q$ for every $k$. Then $(r_k)$ satisfies the
[central limit theorem for lacunary sine sums](lacunary-clt.md): for all real numbers $a < b$, the
Lebesgue measure of the set of $x \in [0, 1]$ with
$a < \frac{1}{\sqrt{n}} \sum_{k=0}^{n-1} \sin(2 \pi r_k x) < b$ tends to
$\frac{1}{\sqrt{\pi}} \int_a^b e^{-y^2} \, dy$, the mass of $(a, b)$ under the normal law with mean
$0$ and variance $1/2$, as $n \to \infty$. In particular this holds for $r_k = 2^k$ and for
$r_k = 2^{k^2}$.

This is the case of unit coefficients of the Salem–Zygmund theorem, which normalises a lacunary sum
$\sum_{k < n} a_k \sin(2 \pi r_k x)$ by $\bigl(\frac12 \sum_{k < n} a_k^2\bigr)^{1/2}$ and obtains the
standard normal law in the limit; with $a_k = 1$ the normaliser is $\sqrt{n/2}$, so dividing by
$\sqrt{n}$ instead gives the normal law with variance $1/2$.

Kac's Problem 161 of the Scottish Book asks whether the same conclusion holds for sequences of
positive integers with $r_n - (r_0 + r_1 + \dots + r_{n-1}) \to +\infty$, and notes that $r_n = 2^n$
does not satisfy this condition. For arbitrary integer sequences the answer is no: the constant
sequence $r_k = -1$ satisfies the condition, since $r_n - (r_0 + \dots + r_{n-1}) = n - 1$, but its
normalized sum $-\sqrt{n} \sin(2 \pi x)$ is not asymptotically normal. Kac's condition differs from
the Hadamard-gap condition of this page: $r_n = 2^n$ has Hadamard gaps with $q = 2$.

## Proof

Write $X_k(x) = \sin(2 \pi r_k x)$ and $S_n = X_0 + \dots + X_{n-1}$ on $[0, 1]$ with Lebesgue measure.
Products of the $X_k$ expand into exponentials $e^{2 \pi i m x}$ with integer $m$, and
$\int_0^1 e^{2 \pi i m x} \, dx = 0$ for $m \ne 0$; as the frequencies are distinct and positive, the $X_k$
are orthogonal with $\int_0^1 X_k^2 = \frac12$. The normal law with variance $\frac12$ is the probability
measure with characteristic function $e^{-t^2/4}$, and it has no atoms. By Lévy's continuity theorem and
the portmanteau theorem it therefore suffices to show that
$\varphi_n(t) = \int_0^1 e^{i t S_n(x)/\sqrt{n}} \, dx \to e^{-t^2/4}$ for every real $t$.

The proof applies Riesz products to blocks of terms. Fix an integer $\ell \ge 1$ with
$q^\ell (q - 1)^2 > 2q$ and integers $p = p(n) \to \infty$ with $p^4/n \to 0$. Split $0, \dots, n - 1$
into blocks of $p$ consecutive indices separated by $\ell$ skipped indices, and let $T_j$ be the sum of
the $X_k$ over the $j$-th block. The skipped indices and an incomplete last block hold
$O(n \ell / p + p) = o(n)$ indices, so by orthogonality and $|e^{ia} - e^{ib}| \le |a - b|$ removing them
changes $\varphi_n(t)$ by $o(1)$. Since each frequency is at least $q$ times the previous one and
consecutive blocks are $\ell$ indices apart, the least frequency of $T_j$ exceeds the sum of the largest
frequencies of the earlier $T_i$, and the same holds for the functions $T_j^2 - \frac{p}{2}$. A product of
such functions from distinct blocks therefore expands into exponentials with nonzero frequencies and has
integral $0$. So the Riesz product
$R_n = \prod_j (1 + i t T_j/\sqrt{n})$ has $\int_0^1 R_n = 1$, the functions $T_j^2 - \frac{p}{2}$ are
orthogonal, and $\int_0^1 |R_n|^2 = \prod_j (1 + t^2 p/(2n)) \le e^{t^2/2}$. An integer $m \ge 1$ has at
most $C(q)$ representations $m = r_a - r_b$ with $a > b$, a number depending only on $q$, since then
$m < r_a \le \frac{q}{q - 1} m$; likewise $m = r_a + r_b$ forces $\frac{m}{2} \le r_a < m$. Expanding
$(T_j^2 - \frac{p}{2})^2$ then gives $\int_0^1 (T_j^2 - \frac{p}{2})^2 = O(p^2)$, so
$\frac{1}{n} \sum_j T_j^2 \to \frac12$ in $L^2$ and hence in measure.

For real $z$ with $|z| \le \frac12$, the Taylor bound for $\log(1 + iz)$ gives
$e^{iz} = (1 + iz) e^{-z^2/2 + \rho(z)}$ with $|\rho(z)| \le |z|^3$. Put $z_j = t T_j/\sqrt{n}$, so that
$|z_j| \le |t| p/\sqrt{n} \to 0$ and $\sum_j |z_j|^3 \le |t|^3 p^2/\sqrt{n} \to 0$. Then
$e^{i t \sum_j T_j/\sqrt{n}} = R_n g_n$ with $g_n = \exp\bigl(-\frac12 \sum_j z_j^2 + \sum_j \rho(z_j)\bigr)$,
$|g_n| \le 2$ for large $n$, and $g_n \to e^{-t^2/4}$ in measure. By the Cauchy–Schwarz inequality and the
bounded convergence theorem, $\int_0^1 R_n (g_n - e^{-t^2/4}) \to 0$, and as $\int_0^1 R_n = 1$ this gives
$\varphi_n(t) \to e^{-t^2/4}$.

## Informally uses

- [Lévy's continuity theorem](../../characteristic-functions/levy-continuity-theorem/levy-continuity-of-char-fun.md): the proof above reduces the limit law to convergence of the characteristic functions $\varphi_n(t) \to e^{-t^2/4}$.
- [Bounded convergence theorem](../../../MeasureTheory/integration/bounded-convergence-theorem/tendsto-integral-of-bounded-convergence.md): the proof above uses it for $\int_0^1 R_n (g_n - e^{-t^2/4}) \to 0$.

## Sources

- R. Salem and A. Zygmund, "On lacunary trigonometric series", Proceedings of the National Academy of
  Sciences of the United States of America 33 (1947).
- M. Kac, Problem 161 of the Scottish Book.
