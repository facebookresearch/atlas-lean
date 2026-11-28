# Exponential growth rate of k-noncrossing RNA structures

**Definitions.** A diagram on $\{1,\dots,n\}$ is a set of arcs $(i,j)$, $i<j$, with every vertex of degree at most $1$. It is **$k$-noncrossing** if it contains no $k$ mutually crossing arcs $(i_1,j_1),\dots,(i_k,j_k)$ with $i_1<\dots<i_k<j_1<\dots<j_k$. A **$k$-noncrossing RNA structure** is a $k$-noncrossing diagram with no $1$-arcs $(i,i+1)$; $k=2$ gives RNA secondary structures and $k\ge 3$ allows pseudoknots. Let ${\sf S}_k(n)$ be the number of such structures on $n$ vertices and $f_k(2n,0)$ the number of $k$-noncrossing perfect matchings on $2n$ points.

**Functional equation.** For $|z|$ below the radius of convergence,

$$\sum_{n\ge 0}{\sf S}_k(n)\,z^{n+1} = \sum_{n\ge 0} f_k(2n,0)\left(\frac{z}{z^2-z+1}\right)^{2n+1}.$$

**Theorem.** Let $k\ge 2$ and let $r_k$ be the radius of convergence of $\sum_{n\ge0} f_k(2n,0)z^{2n}$. Then $\sum_n {\sf S}_k(n)z^n$ has a real dominant singularity at

$$\rho_k = \frac{1+r_k^{-1}}{2} - \sqrt{\Big(\frac{1+r_k^{-1}}{2}\Big)^2 - 1},$$

and ${\sf S}_k(n)$ grows exponentially at rate $1/\rho_k$, that is, $\lim_{n\to\infty}{\sf S}_k(n)^{1/n} = 1/\rho_k$.

For $k=2$, $f_2(2n,0)$ is the Catalan number $C_n$, $r_2 = 1/2$ and $1/\rho_2 = (3+\sqrt5)/2$. For $k=3$, $f_3(2n,0) = C_{n+2}C_n - C_{n+1}^2$, $r_3 = 1/4$ and $1/\rho_3 = (5+\sqrt{21})/2$.

## Expansion

The functional equation comes from inclusion–exclusion over $1$-arcs, ${\sf S}_k(n) = \sum_b (-1)^b\binom{n-b}{b}\sum_\ell f_k(n-2b,\ell)$, together with $f_k(n,\ell) = \binom{n}{\ell}f_k(n-\ell,0)$. Since the coefficients are nonnegative, Pringsheim's theorem places the dominant singularity on the positive real axis. It is the smallest positive $z$ at which $\vartheta(z) = z/(z^2-z+1)$ reaches $r_k$. Solving $z/(z^2-z+1) = r_k$ gives $z^2 - (1 + r_k^{-1})z + 1 = 0$, whose smaller root is $\rho_k$. Hadamard's formula then gives the growth rate. The $k$-noncrossing matchings are counted by the Bessel-determinant generating function $\det[I_{i-j}(2x) - I_{i+j}(2x)]_{i,j=1}^{k-1}$ (Grabiner–Magyar, Chen et al.).

## Sources

- E. Y. Jin and C. M. Reidys, "Asymptotic Enumeration of RNA Structures with Pseudoknots", arXiv:0706.3137 (2007), Definition 1, Theorem 1, Lemma 1 and Theorem 2, <https://doi.org/10.48550/arXiv.0706.3137>.
- Published version: E. Y. Jin and C. M. Reidys, "Asymptotic Enumeration of RNA Structures with Pseudoknots", Bulletin of Mathematical Biology 70 (2008), 951–970, <https://doi.org/10.1007/s11538-007-9265-2>.
