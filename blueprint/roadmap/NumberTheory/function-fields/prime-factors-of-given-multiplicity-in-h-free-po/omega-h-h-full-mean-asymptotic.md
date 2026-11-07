# Mean of $\omega_h$ over $h$-full polynomials

Let $F$ be a finite field with $q$ elements,
let $h \ge 2$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of unity, and let
$\varepsilon > 0$. Write $N_h \cap M_n$ for the set of monic polynomials $f$ of degree $n$ over $F$
that are $h$-full (if a monic irreducible $P$ divides $f$, then so does $P^h$), and $\omega_h(f)$
for the number of monic irreducible $P$ that divide $f$ exactly $h$ times. For monic irreducible
$P$ and $j < h$ put $|P| = q^{\deg P}$, $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$ with $q^{1/h} > 0$,
and $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$. Let
$\kappa_j = \sum_P (K(P, h, j) - |P|^{-1})$ and
$\Pi_j = \prod_P (1 - |P|^{-1})(1 + |P|^{-1}(1 - y_{P,j})^{-1})$, with sum and product over monic
irreducible $P$, and for $X = (X_j)_j$ put
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j=0}^{h-1} \xi^{jn} \Pi_j X_j$. Let $B_1$ be the
function field Mertens constant and $L_n = \log(n/h)$. Then, as $n \to \infty$, the mean
of $\omega_h$ over $N_h \cap M_n$ is $L_n + B_1 + W_n(\kappa) + O(n^{\varepsilon - 1})$.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 5, Equation (8) (`integers-2025-A9-thm-5`).
