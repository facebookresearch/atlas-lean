# Approximation by simple functions

Let $f : \alpha \to [0, \infty]$ be a measurable function on a measurable space. There are simple
functions $\varphi_n : \alpha \to [0, \infty]$ with $\varphi_0 \le \varphi_1 \le \cdots \le f$ and
$\varphi_n(a) \to f(a)$ for every $a$; moreover the convergence is uniform on each set
$\{f \le B\}$ with $B \in [0, \infty)$: for every $\varepsilon \in (0, \infty]$ there is $N$ with
$f(a) - \varphi_n(a) < \varepsilon$ for all $n \ge N$ and all $a$ with $f(a) \le B$, where the
subtraction in $[0, \infty]$ is truncated at $0$.

## Idea

This is the first step in building the Lebesgue integral of a nonnegative function: integrate
the simple functions $\varphi_n$, which only involves measures of sets, and pass to the limit,
which the monotone convergence theorem shows to be independent of the chosen sequence. The
sequence used here rounds $f$ down: $\varphi_n(a)$ is the largest of the first $n$ nonnegative
rationals, in a fixed enumeration, that lie below $f(a)$, or $0$ if there is none. It increases
with $n$, and density of the rationals makes it approach $f$ uniformly wherever $f$ is bounded.

## Statements

- [Approximation of nonnegative measurable functions by simple functions](exists-monotone-tendsto.md)
- [The standard simple approximations converge uniformly where the function is bounded](eapprox-sub-lt-of-le.md): the uniformity for the explicit sequence.
