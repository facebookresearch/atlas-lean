# Second moment of $\omega_k$ over $h$-full polynomials for $k > h$

Let $F$ be a finite
field with $q$ elements, let $2 \le h < k$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of
unity and let $\varepsilon > 0$. Write $M_n$ for the set of monic polynomials of degree $n$ over
$F$, $N_h$ for the set of $h$-full monic polynomials, $|P| = q^{\deg P}$, and $\omega_k(f)$ for the
number of monic irreducible $P$ dividing $f$ whose multiplicity in $f$ is exactly $k$. For $j < h$
and a monic irreducible $P$ put $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$, where $q^{1/h}$ is the
positive real root, $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$ and
$b_P(j) = |P| (q^{1/h}\xi^j)^{-k \deg P} K(P, h, j)$, and let
$\Pi_j = \prod_P (1 - 1/|P|)(1 + 1/(|P|(1 - y_{P,j})))$, where sums and products over $P$ run
over the monic irreducible polynomials. For $X = (X_0, \dots, X_{h-1}) \in \mathbb{C}^h$ let
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j\lt h} \xi^{jn} \Pi_j X_j$. Then the mean of
$\omega_k^2$ over $N_h \cap M_n$ equals $W_n(X) + O(q^{-n/(h(h+1)) + \varepsilon n})$ as
$n \to \infty$, where $X_j = (\sum_P b_P(j))^2 - \sum_P b_P(j)^2 + \sum_P b_P(j)$.

This is the reading of the paper's proof. The printed statement has
$\sum_P b_P^2 - (\sum_P b_P)^2$ (with $b_P = b_P(j)$) with the signs swapped, contradicting the
computation of the second derivative in $z$ of the paper's generating function $B_{k,N_h}(u, z)$
at the end of the proof (page 31).

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 7.
