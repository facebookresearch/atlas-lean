# Rademacher type of a Banach space

A real normed space $X$ has (Rademacher) type $p$ if there is one constant $C$ such that for every $n$ and
every family $x_1, \dots, x_n \in X$,
$2^{-n} \sum_{\varepsilon \in \{-1, 1\}^n} \|\sum_i \varepsilon_i x_i\| \le C (\sum_i \|x_i\|^p)^{1/p}$.
The left side is the [Rademacher average](rademacher-average.md). The definition is written for every real
$p$, but for $p \le 0$ the right side is not an $\ell_p$ expression. Every space has type $p$ for
$0 < p \le 1$ (take $C = 1$).
