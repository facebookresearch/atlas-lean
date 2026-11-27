# Generating function and asymptotics of lv1-shapes of k-noncrossing RNA structures

With the notation of the lv5-shape article ($k$-noncrossing, $\sigma$-canonical RNA structures, the core map $c$ collapsing each stack to one arc, ${\bf F}_k(z) = \sum_n f_k(2n,0) z^n$ the generating function of $k$-noncrossing matchings, $\rho_k = 1/(2k-2)$), the **lv1-shape** of a structure $\delta$ is obtained by taking the core, replacing every maximal segment of consecutive unpaired vertices by a single unpaired vertex, and relabeling. Unlike lv5-shapes, lv1-shapes keep the positions of unpaired regions, but not their lengths.

**Theorem 4.1.** Let $j_k(n,h)$ count lv1-shapes of length $n$ with $h$ arcs, ${\bf J}_k(z,u) = \sum_{n,h} j_k(n,h) z^n u^h$ and ${\bf J}_k(z) = {\bf J}_k(z,1)$. For $k \ge 2$,

$$ {\bf J}_k(z,u) = \frac{(1+z)(1+uz^2)}{uz^3 + 2uz^2 + 1}\, {\bf F}_k\!\left( \frac{(1+z)^2 (1+uz^2)\, u z^2}{(uz^3 + 2uz^2 + 1)^2} \right), $$

and for $2 \le k \le 9$, $j_k(n) \sim c'_k\, n^{-((k-1)^2 + (k-1)/2)} (\mu'_k)^{-n}$, where $\mu'_k$ is the minimal positive solution of $\frac{(1+z)^2(1+z^2) z^2}{(z^3 + 2z^2 + 1)^2} = \rho_k^2$.

**Theorem 4.2.** Let ${\sf lv}^1_{k,\sigma}(n)$ be the number of distinct lv1-shapes of all $k$-noncrossing, $\sigma$-canonical structures of length $n$. Its generating function is

$$ {\bf Lv}^1_{k,\sigma}(x) = \frac{(1+x)(1+x^{2\sigma})}{(1-x)(x^{2\sigma+1} + 2x^{2\sigma} + 1)}\, {\bf F}_k\!\left( \frac{(1+x)^2 x^{2\sigma} (1 + x^{2\sigma})}{(x^{2\sigma+1} + 2x^{2\sigma} + 1)^2} \right) - \frac{x}{1-x}, $$

and for $2 \le k \le 9$, $1 \le \sigma \le 10$, ${\sf lv}^1_{k,\sigma}(n) \sim c'_{k,\sigma}\, n^{-((k-1)^2 + (k-1)/2)} \chi_{k,\sigma}^{-n}$, with $\chi_{k,\sigma}$ the minimal positive solution of $\frac{(1+x)^2 x^{2\sigma}(1+x^{2\sigma})}{(x^{2\sigma+1} + 2x^{2\sigma} + 1)^2} = \rho_k^2$.

The source's eq. (39) prints the formula without the term $-x/(1-x)$. Its $h=0$ term $(j_k(0,0)+j_k(1,0)x)/(1-x)=(1+x)/(1-x)$ then counts 2 shapes without arcs at every length $n\ge1$, where there is one (a structure of length $n\ge1$ without arcs has the one-vertex shape); subtracting $x/(1-x)$ corrects this and leaves the asymptotics unchanged.

## Depends on

- [Generating function and asymptotics of lv5-shapes of k-noncrossing RNA structures](generating-function-of-lv5-shapes-of-k-noncrossing-structures.md)

## Expansion

The proof follows the lv5 case. An lv1-shape is a core in which every maximal unpaired segment has length one, so it is determined by an lv5-shape (its underlying matching after deleting unpaired vertices) together with the choice of which gaps carry a single unpaired vertex; the core condition restricts which gaps may stay empty. Encoding these choices turns the bivariate generating function of lv5-shapes, and through it ${\bf F}_k$, into the stated closed forms, with $u$ marking arcs. For induced shapes of fixed length, each shape arc is realized by a stack of at least $\sigma$ arcs and each isolated vertex by a nonempty unpaired segment. The asymptotics again come from Proposition 1: the inner algebraic function reaches the dominant singularity $\rho_k^2$ of ${\bf F}_k$ at a point where it is analytic, so only the exponential growth rate changes.

## Sources

- Christian M. Reidys, Rita R. Wang, "Shapes of RNA Pseudoknot Structures", Journal of Computational Biology 17 (2010), 1575–1590, <https://doi.org/10.1089/cmb.2010.0006>. Published version of arXiv:0906.3999, cited next; locators there refer to the arXiv version.
- Christian M. Reidys, Rita R. Wang, "Shapes of RNA pseudoknot structures", arXiv (2009). Section 4, Theorems 4.1 and 4.2. <https://doi.org/10.48550/arXiv.0906.3999>
