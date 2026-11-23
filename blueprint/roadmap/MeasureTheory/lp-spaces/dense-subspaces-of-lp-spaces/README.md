# Density of continuous functions vanishing at the endpoints in L^p

Let $a < b$, $1 \le p < \infty$ and $E$ a real normed space. For every $f : \mathbb{R} \to E$ in
$L^p([a, b])$, for Lebesgue measure on $[a, b]$, and every $\varepsilon > 0$, there is a continuous
$g : \mathbb{R} \to E$ with $g(a) = g(b) = 0$ and $\|f - g\|_{L^p([a, b])} < \varepsilon$.

## Idea

Continuous functions are dense in $L^p([a, b])$ for $p < \infty$; the point is to make them vanish
at the endpoints without spoiling the approximation. Multiply a continuous approximant $g_0$ by a
piecewise linear cutoff $\varphi_n$ with values in $[0, 1]$, equal to $0$ at $a$ and $b$ and to $1$
on $[a + \delta_n, b - \delta_n]$, where $\delta_n \to 0$. The error $g_0 - \varphi_n g_0$ is
bounded by $|g_0|$ and vanishes outside two intervals of length $\delta_n$, so its $L^p$ norm
tends to $0$ by dominated convergence. The statement fails for $p = \infty$, where uniform limits
of continuous functions are continuous. The other statements construct the cutoff and record its
properties.

## Statements

- [Continuous functions vanishing at the endpoints are dense in $L^p$ of a compact interval](exists-continuous-vanishing-endpoints-e.md)
- [Cutoff approximants](cutoff-approx.md): construction used in the proof.
- [Continuity of the cutoff approximants](cutoff-approx-continuous.md): construction used in the proof.
- [Cutoff approximants vanish at the left endpoint](cutoff-approx-eq-zero-left.md): construction used in the proof.
- [Cutoff approximants vanish at the right endpoint](cutoff-approx-eq-zero-right.md): construction used in the proof.
- [Cutoff approximants stay in $L^p$](cutoff-approx-mem-lp.md): construction used in the proof.
- [Pointwise bound on the cutoff error](norm-sub-cutoff-approx-le.md): construction used in the proof.
- [Vanishing cutoff factor](vanishing-cutoff.md): construction used in the proof.
- [Continuity of the vanishing cutoff factor](vanishing-cutoff-continuous.md): construction used in the proof.
- [The vanishing cutoff factor equals one on its plateau](vanishing-cutoff-eq-one.md): construction used in the proof.
- [The vanishing cutoff factor vanishes at the left endpoint](vanishing-cutoff-eq-zero-left.md): construction used in the proof.
- [The vanishing cutoff factor vanishes at the right endpoint](vanishing-cutoff-eq-zero-right.md): construction used in the proof.
- [The vanishing cutoff factor is at most one](vanishing-cutoff-le-one.md): construction used in the proof.
- [The vanishing cutoff factor is nonnegative](vanishing-cutoff-nonneg.md): construction used in the proof.

## Background

- [Density of simple functions in L^p](../density-of-simple-functions-in-lp/README.md): scalar simple approximation, for any measure
