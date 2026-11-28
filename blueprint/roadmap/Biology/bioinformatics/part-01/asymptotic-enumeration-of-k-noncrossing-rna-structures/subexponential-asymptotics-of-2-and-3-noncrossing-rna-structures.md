# Subexponential asymptotics of 2- and 3-noncrossing RNA structures

**Setting.** Let ${\sf S}_k(n)$ be the number of $k$-noncrossing RNA structures on $n$ vertices: diagrams with vertex degrees at most $1$, no $1$-arcs $(i,i+1)$, and no $k$ mutually crossing arcs.

**Theorem.** As $n\to\infty$, the number of RNA secondary structures ($k=2$) satisfies

$${\sf S}_2(n) \sim \frac{1.1002}{\sqrt n}\left(\frac{1}{n+1} - \frac{1}{8n(n+1)} + \frac{1}{128n^3} + \frac{5}{1024n^4} + O(n^{-5})\right)\left(\frac{3+\sqrt5}{2}\right)^n,$$

so ${\sf S}_2(n) \asymp n^{-3/2}\big((3+\sqrt5)/2\big)^n$. The number of $3$-noncrossing RNA structures satisfies

$${\sf S}_3(n) \sim \frac{10.4724\cdot 4!}{n(n-1)\cdots(n-4)}\left(\frac{5+\sqrt{21}}{2}\right)^n,$$

so ${\sf S}_3(n) \asymp n^{-5}\big((5+\sqrt{21})/2\big)^n$. Allowing pseudoknots (crossings of two arcs, but not of three) thus raises the exponential growth rate from about $2.618$ to about $4.791$. It also changes the polynomial correction from $n^{-3/2}$ to $n^{-5}$.

## Expansion

Both results come from singularity analysis of the generating function

$$\sum_{n\ge0}{\sf S}_k(n)z^n = \frac{1}{z^2-z+1}\sum_{n\ge0}f_k(2n,0)\left(\frac{z}{z^2-z+1}\right)^{2n},$$

where $f_k(2n,0)$ counts $k$-noncrossing perfect matchings. For $k=2$ the inner series is the Catalan generating function, which has a square-root singularity. This produces the algebraic expansion and, through the Flajolet–Odlyzko transfer theorem, the $n^{-3/2}$ factor. For $k=3$ the matchings are counted by $C_{n+2}C_n - C_{n+1}^2$, whose generating function $\sum_n f_3(2n,0)y^n$ continues analytically as a Legendre function with a single dominant singularity at $y = 1/16$. Composed with $\vartheta(z) = (z/(z^2-z+1))^2$, this gives six singularities of distinct moduli, the dominant one being $\rho_3 = (5-\sqrt{21})/2$, where the expansion is $O\big((\rho_3-z)^4\ln\frac{1}{\rho_3-z}\big)$. The logarithmic case of the transfer theorem, $[z^n]\,(1-z)^r\ln\frac{1}{1-z} = (-1)^r r!/(n(n-1)\cdots(n-r))$ for $n>r$, with $r=4$, gives the falling-factorial denominator. The constants $1.1002$ and $10.4724$ are numerical evaluations of the singular expansions.

## Depends on

- [Exponential growth rate of k-noncrossing RNA structures](exponential-growth-rate-of-k-noncrossing-rna-structures.md)

## Proof depends on

- [Closed form of the Catalan generating function](../../../../Combinatorics/catalan-numbers-lattice-paths/catalan-numbers/catalan-numbers/catalan-generating-function-sqrt.md)

## Sources

- E. Y. Jin and C. M. Reidys, "Asymptotic Enumeration of RNA Structures with Pseudoknots", arXiv:0706.3137 (2007), Lemma 2 and Theorems 3–5, <https://doi.org/10.48550/arXiv.0706.3137>.
- Published version: E. Y. Jin and C. M. Reidys, "Asymptotic Enumeration of RNA Structures with Pseudoknots", Bulletin of Mathematical Biology 70 (2008), 951–970, <https://doi.org/10.1007/s11538-007-9265-2>.
