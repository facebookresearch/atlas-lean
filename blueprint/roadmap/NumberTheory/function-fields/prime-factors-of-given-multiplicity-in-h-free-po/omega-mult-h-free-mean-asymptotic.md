# Mean of $\omega_k$ over $h$-free polynomials

Let $F$ be a finite field with $q$ elements,
let $h, k$ be natural numbers with $1 < k < h$, and let $\varepsilon > 0$. Write $S_h \cap M_n$ for
the set of monic polynomials $f$ of degree $n$ over $F$ that are $h$-free (no $P^h$ with $P$ monic
irreducible divides $f$), and $\omega_k(f)$ for the number of monic irreducible $P$ that divide $f$
exactly $k$ times. For monic irreducible $P$ put $|P| = q^{\deg P}$ and
$a_P = |P|^{h-k-1}(|P| - 1)/(|P|^h - 1)$, and let $S_{h,k} = \sum_P a_P$, the sum over monic
irreducible $P$. Then, as $n \to \infty$, the mean of $\omega_k$ over
$S_h \cap M_n$ is $S_{h,k} + O(q^{n/k - n + \varepsilon n})$.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 3, Equation (6) (`integers-2025-A9-thm-3`).
