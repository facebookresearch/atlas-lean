# Binet asymptotics for weighted generalized Fibonacci sequences

Let $r \ge 2$, let
$A_1, \dots, A_r$ and $c_1, \dots, c_r$ be nonnegative real numbers with $A_r > 0$ and $c_j > 0$
for some $j$, and suppose that the indices $j$ with $A_j > 0$ have greatest common divisor $1$.
Let $a_0, a_1, a_2, \dots$ be the real sequence with $a_n = c_{n+1}$ for $0 \le n < r$ and
$a_n = \sum_{j=1}^{r} A_j a_{n-j}$ for $n \ge r$, and let $p(x) = x^r - \sum_{j=1}^{r} A_j x^{r-j}$
be its characteristic polynomial. Let $\lambda > 0$ be a root of $p$ that is not a root of the
derivative $p'$, and such that every complex root $z$ of $p$ satisfies $|z| \le \lambda$, with
$|z| = \lambda$ only for $z = \lambda$. Then there is a constant $C > 0$ such that
$a_n = C \lambda^n + o(\lambda^n)$ as $n \to \infty$, and $a_{n+1} / a_n \to \lambda$.

The source indexes the sequence from $1$; the $a_n$ here is the source's $a_{n+1}$, and $A_j$,
$c_j$ are the source's weights and initial values.

## Sources

- Passawan Noppakaew and Thanakorn Prinyasart, "Complete Sequences of Weighted r-Generalized Fibonacci Powers," Journal of Integer Sequences 24 (2021), Article 21.5.4, Proposition (label `binet`), lines 119–126, https://cs.uwaterloo.ca/journals/JIS/VOL24/Prinyasart/prin3.tex Proves `Wanted` entry `binet`. It follows from `binet_general`; the hypotheses `hlam_simple` and `hlam_dom` are unused and keep the source's shape.
