# The saved first cut attains the saved revenue

Let $p = (p_0, \dots, p_{n-1})$ be a
price vector with entries in an additive commutative monoid carrying a linear order, where
$p_{\ell - 1}$ is the price of a piece of length $\ell$. Let $r = (r_0, \dots, r_n)$ be the
revenue table and $s = (s_1, \dots, s_n)$ the saved first cuts computed by the extended bottom-up
rod-cutting algorithm, with $s_j$ stored as entry $j - 1$ of the cut vector. For every $j$ with
$0 < j \le n$, the cut $\ell = s_j$ satisfies $1 \le \ell \le j$ and
$p_{\ell - 1} + r_{j - \ell} = r_j$, and every $\ell'$ with $1 \le \ell' < \ell$ satisfies
$p_{\ell' - 1} + r_{j - \ell'} < r_j$.
