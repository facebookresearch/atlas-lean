# Generating function and asymptotics of lv5-shapes of k-noncrossing RNA structures

**Setting.** A $k$-noncrossing diagram on vertices $1, \dots, n$ is a set of arcs $(i,j)$, $i < j$, each vertex in at most one arc, with no $k$ mutually crossing arcs; an RNA structure is $\sigma$-canonical if every stack (maximal sequence of nested parallel arcs $(i-\ell, j+\ell), \dots, (i,j)$) has at least $\sigma$ arcs. Let $f_k(2n,0)$ be the number of $k$-noncrossing matchings on $2n$ vertices and ${\bf F}_k(z) = \sum_{n \ge 0} f_k(2n,0) z^n$; ${\bf F}_k$ is $D$-finite with unique dominant singularity $\rho_k^2$, $\rho_k = 1/(2k-2)$, and $f_k(2n,0) \sim \tilde c_k\, n^{-((k-1)^2 + (k-1)/2)} (2k-2)^{2n}$. The **core** $c(\delta)$ collapses every stack to a single arc and relabels. The **lv5-shape** of $\delta$ is obtained by deleting all unpaired vertices and then taking the core; it is a $k$-noncrossing matching in which every stack has size one, and it forgets stack lengths, interior loops and unpaired regions.

**Theorem 3.1.** Let $i_k(n,m)$ be the number of lv5-shapes with $2n$ vertices and $m$ arcs of the form $(i, i+1)$, ${\bf I}_k(z,u) = \sum_{n,m} i_k(n,m) z^n u^m$ and ${\bf I}_k(z) = {\bf I}_k(z,1)$. For $k \ge 2$,

$$ {\bf I}_k(z,u) = \frac{1+z}{1+2z-zu}\, {\bf F}_k\!\left( \frac{z(1+z)}{(1+2z-zu)^2} \right), \qquad {\bf I}_k(z) = {\bf F}_k\!\left( \frac{z}{1+z} \right), $$

and for $2 \le k \le 9$, $i_k(n) \sim c_k\, n^{-((k-1)^2 + (k-1)/2)} \mu_k^{-n}$, where $\mu_k$ is the minimal positive solution of $z/(1+z) = \rho_k^2$, i.e. $\mu_k = \rho_k^2/(1-\rho_k^2)$.

**Theorem 3.2.** Let ${\sf lv}^5_{k,\sigma}(n)$ be the number of distinct lv5-shapes of all $k$-noncrossing, $\sigma$-canonical structures of length $n$, with generating function ${\bf Lv}^5_{k,\sigma}(x)$. Then

$$ {\bf Lv}^5_{k,\sigma}(x) = \frac{1 + x^{2\sigma}}{(1-x)(1 + 2x^{2\sigma} - x^{2\sigma+1})}\, {\bf F}_k\!\left( \frac{x^{2\sigma}(1 + x^{2\sigma})}{(1 + 2x^{2\sigma} - x^{2\sigma+1})^2} \right), $$

and for $2 \le k \le 9$, $1 \le \sigma \le 10$, ${\sf lv}^5_{k,\sigma}(n) \sim c_{k,\sigma}\, n^{-((k-1)^2 + (k-1)/2)} \zeta_{k,\sigma}^{-n}$ with $\zeta_{k,\sigma}$ the minimal positive solution of $\frac{x^{2\sigma}(1 + x^{2\sigma})}{(1 + 2x^{2\sigma} - x^{2\sigma+1})^2} = \rho_k^2$.

## Expansion

Every lv5-shape is the core of a $k$-noncrossing matching, and the counts $g_k(n,m)$ of $k$-noncrossing matchings on $2n$ vertices with $m$ arcs of length one satisfy $(m+1) g_k(n+1,m+1) = (m+1) g_k(n,m+1) + (2n+1-m) g_k(n,m)$, with ${\bf G}_k(x,y) = \frac{1}{x+1-yx} {\bf F}_k\bigl(x/(x+1-yx)^2\bigr)$ (Lemma 2.2). Relating matchings to their cores by inflating each shape arc into a stack yields ${\bf I}_k(z,u)$ by inverting this substitution. For Theorem 3.2 the same relation is applied to $\sigma$-canonical structures of a given length, whose generating function is a composition of ${\bf F}_k$ with an explicit rational function. The asymptotics follow from Proposition 1: when an algebraic inner function $\vartheta$ with $\vartheta(0) = 0$ is analytic at the unique dominant singularity $\gamma$ of ${\bf F}_k(\vartheta(z))$ and $\vartheta(\gamma) = \rho_k^2$, the coefficients keep the polynomial exponent of $f_k(2n,0)$ and grow like $\gamma^{-n}$. The range $k \le 9$ reflects the explicitly computed singular sets of ${\bf F}_k$.

## Sources

- Christian M. Reidys, Rita R. Wang, "Shapes of RNA Pseudoknot Structures", Journal of Computational Biology 17 (2010), 1575–1590, <https://doi.org/10.1089/cmb.2010.0006>. Published version of arXiv:0906.3999, cited next; locators there refer to the arXiv version.
- Christian M. Reidys, Rita R. Wang, "Shapes of RNA pseudoknot structures", arXiv (2009). Section 2 (Theorem 2.1, Proposition 1, Lemma 2.2), Section 3, Theorems 3.1 and 3.2. <https://doi.org/10.48550/arXiv.0906.3999>
