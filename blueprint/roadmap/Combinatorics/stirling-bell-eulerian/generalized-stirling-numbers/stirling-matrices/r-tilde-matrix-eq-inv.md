# The inverse of the matrix $R_\alpha(n)$

For a sequence
$\alpha = (\alpha_0, \alpha_1, \dots)$ of rationals, let
$\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$ and
$\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$, where
$m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ is the falling factorial. For a natural number $n$,
let $R_\alpha(n)$ and $\tilde R_\alpha(n)$ be the upper triangular $n \times n$ rational
matrices whose $(i, j)$ entries for $1 \le i \le j \le n$ are
$\frac{(-1)^{j-i}}{(j-i)!} \Psi_\alpha(i)$ and $(j-1)^{\underline{i-1}} / \Omega(\alpha, j)$
respectively. If $\prod_{j=1}^{n} \Omega(\alpha, j) \ne 0$, then
$\tilde R_\alpha(n) = R_\alpha(n)^{-1}$.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima Salehy, and Navid Salehy, "Some Identities Involving Stirling Numbers Arising from Matrix Decompositions", Lemma 7.
