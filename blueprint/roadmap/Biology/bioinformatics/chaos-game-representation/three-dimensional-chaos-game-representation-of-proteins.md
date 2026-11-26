# Three-dimensional chaos game representation of proteins

**Construction.** Place the 20 amino acids $\Omega$ at the vertices of a regular dodecahedron inscribed in the unit ball $B$ centred at $X_0 = (1,1,1)$ (so its edge length is $a = 4/(\sqrt3(1+\sqrt5)) \approx 0.7136$). For a protein $\omega_1\omega_2\cdots\omega_N$, define the chaos game points

$$X_0 = (1,1,1), \qquad X_n = (1-u)\,\omega_n + u\, X_{n-1}, \quad n \ge 1,$$

with contraction parameter

$$u = \frac{\sqrt5 - 1}{\sqrt5 + 2\sqrt3 - 1} \approx 0.263.$$

The *ball controlled by* $\omega$ is $B_\omega$, centred at $u X_0 + (1-u)\omega$ with radius $u$; the ball controlled by a dipeptide $\omega_1\omega_2$ is $B_{\omega_1\omega_2}$, centred at $u(1-u)(\omega_1 - X_0) + (u X_0 + (1-u)\omega_2)$ with radius $u^2$.

**Theorem.** For every amino acid sequence of length $N$:
1. $B_\omega$ is inscribed in $B$ at the vertex $\omega$, and $B_{\omega_1\omega_2}$ is inscribed in $B_{\omega_2}$;
2. $X_n \in B_{\omega_n}$ for $1 \le n \le N$, and $X_n \in B_{\omega_{n-1}\omega_n}$ for $2 \le n \le N$;
3. the balls of distinct amino acids have disjoint interiors, and balls of adjacent vertices are tangent;
4. the number of occurrences of $\omega$ (respectively of the dipeptide $\omega_1\omega_2$) equals the number of points $X_n$ in $B_\omega$ (respectively in $B_{\omega_1\omega_2}$);
5. the point $X_n$ determines the prefix $\omega_1\cdots\omega_n$.

## Expansion

Since $X_n - (uX_0 + (1-u)\omega_n) = u(X_{n-1} - X_0)$ and $\|X_{n-1} - X_0\| \le 1$ by induction, $X_n$ lies in $B_{\omega_n}$; iterating once more places it in the radius-$u^2$ ball of the last two letters. Two adjacent vertices are at distance $a$, so the centres of their controlled balls are at distance $(1-u)a$, and tangency $2u = (1-u)a$ gives $u = a/(2+a)$, which equals the stated closed form; non-adjacent vertices are farther apart, so all controlled balls are interior-disjoint. Disjointness at every scale makes the address of $X_n$ unique, which yields both counting statements and the recovery of the prefix, exactly as the quadrant structure does for the two-dimensional DNA representation with $u = 1/2$. Dipeptide counts read off the image give a 400-dimensional feature vector for alignment-free protein comparison.

## Sources

- Z. Sun, S. Pei, R. L. He, S. S.-T. Yau, "A novel numerical representation for proteins: three-dimensional chaos game representation and its extended natural vector", Computational and Structural Biotechnology Journal 18 (2020) 1904–1913, Eq. (1), Table 1, Definitions 1–2 and Theorem 1, <https://doi.org/10.1016/j.csbj.2020.07.004>, PMCID PMC7390779.
