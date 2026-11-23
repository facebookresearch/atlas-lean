# Maximal functions of bounded a.e.-null sequences tend to zero almost everywhere

Let $f_n : \mathbb{R} \to \mathbb{R}$, $n \in \mathbb{N}$, be Lebesgue measurable on $[0, 1]$, with
$f_n(x) \in [0, 1]$ for every $x \in [0, 1]$, and suppose that $f_n(x) \to 0$ for almost every
$x \in [0, 1]$. For $x \in [0, 1]$ let $Mf_n(x) = \sup_I \frac{1}{|I|} \int_I |f_n|$, the supremum
over closed intervals $I = [a, b]$ with $a < b$ and $x \in I \subseteq [0, 1]$. Then $Mf_n(x) \to 0$
for almost every $x \in [0, 1]$.

## Idea

A uniform bound lets almost-everywhere convergence pass to maximal functions. The functions
$g_N = \sup_{n \ge N} f_n$ decrease to $0$ almost everywhere, so $\int g_N \to 0$; the
Hardy–Littlewood maximal inequality bounds the measure of $\{M g_N > t\}$ by a constant times
$\int g_N / t$, and $M f_n \le M g_N$ for $n \ge N$. Without the bound the conclusion fails:
$f_n = n \mathbf{1}_{(0, 1/n)}$ tends to $0$ almost everywhere, but averaging over $[0, x]$ gives
$M f_n(x) \ge 1/x$ once $n \ge 1/x$.

## Statements

- [Maximal functions of bounded a.e.-null sequences tend to zero a.e](ae-tendsto-maximal-zero-of-ae-tendsto-ze.md)
