# Two factorizations of the Stirling-like matrix

Let
$\alpha = (\alpha_0, \alpha_1, \dots)$ be a sequence of rationals. For natural numbers
$i, j \ge 1$ define $S_{i,j}$ and $U_{i,j}$ by $S_{1,j} = U_{1,j} = \alpha_{j-1}$,
$S_{i,1} = \alpha_0$ and $U_{i,1} = 0$ for $i \ge 2$, and, for $i, j \ge 2$,
$S_{i,j} = S_{i-1,j-1} + j \, S_{i-1,j}$ and $U_{i,j} = U_{i-1,j-1} + (j-i+1) \, U_{i-1,j}$;
let $R_{i,j} = \frac{(-1)^{j-i}}{(j-i)!} \Psi_\alpha(i)$ if $i \le j$ and $R_{i,j} = 0$ if
$i > j$, where $\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$. For every natural
number $n$, let $S_\alpha(n)$, $U_\alpha(n)$ and $R_\alpha(n)$ be the $n \times n$ matrices
$(S_{i,j})$, $(U_{i,j})$ and $(R_{i,j})$ with $1 \le i, j \le n$, let
$S(n) = (S(i,j))_{1 \le i, j \le n}$ be the matrix of Stirling numbers of the second kind, and
let $V(n) = (j^{i-1})_{1 \le i, j \le n}$. Then $S_\alpha(n) = S(n) \, U_\alpha(n)$ and
$S_\alpha(n) = V(n) \, R_\alpha(n)$.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima Salehy, and Navid Salehy, "Some Identities Involving Stirling Numbers Arising from Matrix Decompositions", Theorem 3.
