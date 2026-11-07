# Explicit formula for the entries of $U_\alpha$

Let
$\alpha \colon \mathbb{N} \to \mathbb{Q}$ and let $U_\alpha = (U_{i,j})_{i \ge 1, j \ge 0}$ be
given by $U_{i,0} = 0$, $U_{1,j} = \alpha_{j-1}$ for $j \ge 1$, $U_{i,1} = 0$ for $i \ge 2$, and
$U_{i,j} = U_{i-1,j-1} + (j-i+1) \, U_{i-1,j}$ for $i, j \ge 2$. For $k_1 \le k_2$ let
$\Lambda(\alpha, k_1, k_2) = \sum_{l=0}^{k_1-1} \binom{k_1-1}{l}
\frac{(l+k_2-k_1)!}{(k_2-k_1)!} \, \alpha_{l+k_2-k_1}$. Then $U_{i,j} = \Lambda(\alpha, i, j)$
for all $1 \le i \le j$.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima Salehy, and Navid Salehy, "Some Identities Involving Stirling Numbers Arising from Matrix Decompositions", Lemma 1.
