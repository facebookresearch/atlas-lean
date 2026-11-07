# Convergence in the $L^0$ pseudometric is convergence in measure

Let $f$ and
$f_0, f_1, f_2, \ldots$ be Borel measurable functions $\mathbb{R} \to \mathbb{R}$, and let $d$ be
the pseudometric

$$
d(g,h) = \int_{[0,1]} \frac{|g(x) - h(x)|}{1 + |g(x) - h(x)|}\,dx
$$

on such functions, the integral being with respect to Lebesgue measure. Then
$d(f_n, f) \to 0$ as $n \to \infty$ if and only if $f_n \to f$ in measure with respect to
Lebesgue measure on $[0,1]$: for every $\varepsilon > 0$, the Lebesgue measure of
$\{x \in [0,1] : |f_n(x) - f(x)| \ge \varepsilon\}$ tends to $0$ as $n \to \infty$.

The source states this for $L^0([0,1])$, on which $d$ is a metric; here it is stated for
representatives, on which $d$ is only a pseudometric. Both sides depend only on the
almost-everywhere classes of the functions on $[0,1]$, so the two statements say the same thing.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear function spaces and their duals), `benchmark/level2/ma_proofbench_l2_07.lean` at openbmb/ma-proofbench@31bab4c, with the change above.
