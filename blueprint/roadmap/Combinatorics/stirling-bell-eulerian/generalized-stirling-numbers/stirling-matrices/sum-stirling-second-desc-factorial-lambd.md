# Stirling and falling-factorial sum of the $\Lambda$ coefficients

Let
$\alpha \colon \mathbb{N} \to \mathbb{Q}$, let $S(i, k)$ denote the Stirling numbers of the
second kind, let $m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ be the falling factorial, let
$\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$, and for $k_1 \le k_2$
let $\Lambda(\alpha, k_1, k_2) = \sum_{l=0}^{k_1-1} \binom{k_1-1}{l}
\frac{(l+k_2-k_1)!}{(k_2-k_1)!} \, \alpha_{l+k_2-k_1}$. If $i, j \ge 1$ and
$\prod_{k=1}^{\max(i,j)} \Omega(\alpha, k) \ne 0$, then

$$\sum_{k_1=1}^{i} \sum_{k_2=k_1}^{j} S(i,k_1) \, (j-1)^{\underline{k_2-1}} \,
\Lambda(\alpha, k_1, k_2) = j^{i-1} \, \Omega(\alpha, j).$$

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima Salehy, and Navid Salehy, "Some Identities Involving Stirling Numbers Arising from Matrix Decompositions", Proposition 8.
