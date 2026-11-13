# Generating function of $k$-box paths by returns

For $k \in \mathbb{N}$, $F_k(t, x)$ is
the power series in $\mathbb{Z}[t][[x]]$ with constant term $0$ whose coefficient of $x^n$ for
$n \ge 1$ is the sum of $t^{\operatorname{ret}(\mu)}$ over the set $B_n^{(k)}$ of $k$-box paths
$\mu$ of size $n$, where $\operatorname{ret}(\mu)$ is the number of returns of $\mu$; that is,
$F_k(t, x) = \sum_{n \ge 1} \sum_{\mu \in B_n^{(k)}} t^{\operatorname{ret}(\mu)} x^n$.

## Sources

- Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 6.
