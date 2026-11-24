# Second moment of $\omega_h$ over $h$-full polynomials

Let $F$ be a finite field with $q$
elements, let $h \ge 2$, let $\xi \in \mathbb{C}$ be a primitive $h$-th root of unity, and let
$\varepsilon > 0$. Write $N_h \cap M_n$ for the set of monic polynomials $f$ of degree $n$ over $F$
that are $h$-full (if a monic irreducible $P$ divides $f$, then so does $P^h$), and $\omega_h(f)$
for the number of monic irreducible $P$ that divide $f$ exactly $h$ times. For monic irreducible
$P$ and $j < h$ put $|P| = q^{\deg P}$, $y_{P,j} = (q^{1/h}\xi^j)^{-\deg P}$ with $q^{1/h} > 0$,
and $K(P, h, j) = (1 - y_{P,j})/(|P|(1 - y_{P,j}) + 1)$. Let
$\kappa_j = \sum_P (K(P, h, j) - |P|^{-1})$ and
$\Pi_j = \prod_P (1 - |P|^{-1})(1 + |P|^{-1}(1 - y_{P,j})^{-1})$, with sum and product over monic
irreducible $P$, and for $X = (X_j)_j$ put
$W_n(X) = |N_h \cap M_n|^{-1} (q^{n/h}/h) \sum_{j=0}^{h-1} \xi^{jn} \Pi_j X_j$. Let $B_1$ be the
function field Mertens constant and $L_n = \log(n/h)$. Then, as $n \to \infty$,
the mean of $\omega_h^2$ over $N_h \cap M_n$ is
$L_n^2 + (2B_1 + 1 + 2W_n(\kappa)) L_n + B_1^2 + B_1 - \pi^2/6 + W_n(X) + O(n^{\varepsilon - 1})$,
where $X_j = -\sum_P K(P, h, j)^2 + \kappa_j^2 + (2B_1 + 1)\kappa_j$.

This follows the paper's proof: the printed constant term $C_3$ has $-W_n(Z)$ in place of
$W_n(X)$, where $Z_j = \sum_P K(P, h, j)^2 + \kappa_j^2 + (2B_1 + 1)\kappa_j$; this contradicts
the final display of the proof (page 29) and the printed variance.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 5, Equation (9).
