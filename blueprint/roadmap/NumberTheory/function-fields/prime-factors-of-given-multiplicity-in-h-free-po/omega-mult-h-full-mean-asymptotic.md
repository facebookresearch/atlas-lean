# Mean of $\omega_k$ over $h$-full polynomials for $k > h$

Let $F$ be a finite field with
$q$ elements, let $2 \le h < k$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of unity and
let $\varepsilon > 0$. Write $M_n$ for the set of monic polynomials of degree $n$ over $F$, $N_h$
for the set of $h$-full monic polynomials, $|P| = q^{\deg P}$, and $\omega_k(f)$ for the number of
monic irreducible $P$ dividing $f$ whose multiplicity in $f$ is exactly $k$. For $j < h$ and a
monic irreducible $P$ put $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$, where $q^{1/h}$ is the positive
real root, $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$ and
$b_P(j) = |P| (q^{1/h}\xi^j)^{-k \deg P} K(P, h, j)$, and let
$\Pi_j = \prod_P (1 - 1/|P|)(1 + 1/(|P|(1 - y_{P,j})))$, where sums and products over $P$ run
over the monic irreducible polynomials. For $X = (X_0, \dots, X_{h-1}) \in \mathbb{C}^h$ let
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j\lt h} \xi^{jn} \Pi_j X_j$. Then the mean of
$\omega_k$ over $N_h \cap M_n$ equals
$W_n\bigl(\sum_P b_P(0), \dots, \sum_P b_P(h-1)\bigr) + O(q^{-n/(h(h+1)) + \varepsilon n})$ as
$n \to \infty$.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 7 (`integers-2025-A9-thm-7`).
