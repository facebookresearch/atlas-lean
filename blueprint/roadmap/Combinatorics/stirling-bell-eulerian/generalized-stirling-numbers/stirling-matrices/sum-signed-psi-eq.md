# First-kind Stirling formula for $\Lambda(\alpha, i, j)$

Let
$\alpha \colon \mathbb{N} \to \mathbb{Q}$, let $s(i, k)$ denote the signed Stirling numbers of
the first kind, let $\Psi_\alpha(k) = \sum_{l=0}^{k-1} \alpha_l / (k-1-l)!$, and for
$k_1 \le k_2$ let $\Lambda(\alpha, k_1, k_2) = \sum_{l=0}^{k_1-1} \binom{k_1-1}{l}
\frac{(l+k_2-k_1)!}{(k_2-k_1)!} \, \alpha_{l+k_2-k_1}$. Then for all $i, j \ge 1$ the sum

$$\sum_{k_1=1}^{i} \sum_{k_2=1}^{j} s(i,k_1) \, k_2^{k_1-1} \, \frac{(-1)^{j-k_2}}{(j-k_2)!} \,
\Psi_\alpha(k_2)$$

equals $\Lambda(\alpha, i, j)$ if $i \le j$ and $0$ if $i > j$.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima Salehy, and Navid Salehy, "Some Identities Involving Stirling Numbers Arising from Matrix Decompositions", Proposition 9.
