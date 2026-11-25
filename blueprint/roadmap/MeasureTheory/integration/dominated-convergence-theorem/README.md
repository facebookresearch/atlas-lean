# Dominated convergence theorem for nonnegative functions

Let $\mu$ be a measure on a set $\alpha$ with a σ-algebra, and let $F_n \colon \alpha \to [0, \infty]$ be measurable
functions with $F_n \to f$ almost everywhere and $F_n \le g$ almost everywhere for every $n$, for some $g$ with
$\int g \, d\mu < \infty$. Then $\int F_n \, d\mu \to \int f \, d\mu$. This is the dominated convergence theorem for
functions with values in $[0, \infty]$: for measurable real or complex $f_n$ and $f$ with $f_n \to f$ almost everywhere
and $|f_n| \le g$, it applies to $|f_n - f| \le 2g$ and gives $\int |f_n - f| \, d\mu \to 0$, hence
$\int f_n \, d\mu \to \int f \, d\mu$.

## Idea

A single dominating function of finite integral keeps mass from escaping, which is how convergence of integrals fails
without it: on $\mathbb{R}$, the functions $\chi_{[n, n+1]}$ and $n \chi_{(0, 1/n)}$ tend to $0$ pointwise, but each has
integral $1$. Since $f$ and $g$ need not be measurable, the proof works with two measurable functions instead:
$\liminf_n F_n$, which equals $f$ almost everywhere and so has the same integral, and $h = \sup_n F_n$, which satisfies
$h \le g$ almost everywhere, since the countably many exceptional null sets have a null union, so that
$\int h \, d\mu < \infty$. Fatou's lemma applied to the $F_n$ gives $\int f \, d\mu \le \liminf_n \int F_n \, d\mu$, and
applied to the functions $h - F_n \ge 0$, which tend to $h - f$ almost everywhere, it gives
$\limsup_n \int F_n \, d\mu \le \int f \, d\mu$.

## Statements

- [Dominated convergence theorem for nonnegative functions](tendsto-lintegral-of-dominated-convergence.md)

## Background

- [Fatou's lemma](../nonnegative-lebesgue-integral/fatou-s-lemma/README.md): used in the proof
- [Lebesgue integral](../nonnegative-lebesgue-integral/lebesgue-integral/README.md): the integral

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 3.31 (version read: the open-access PDF dated 12 June 2026).
