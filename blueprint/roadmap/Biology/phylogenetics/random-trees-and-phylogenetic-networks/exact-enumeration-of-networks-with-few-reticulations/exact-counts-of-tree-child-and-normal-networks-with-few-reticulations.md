# Exact counts of tree-child and normal networks with few reticulations

**Setting.** A rooted binary phylogenetic network is a connected directed acyclic graph without double edges with a unique root (in-degree $0$, out-degree $2$), tree vertices (in-degree $1$, out-degree $2$), reticulation vertices (in-degree $2$, out-degree $1$) and leaves (in-degree $1$, out-degree $0$); with $\ell$ leaves and $k$ reticulations it has $2\ell + 2k - 1$ vertices; it is **tree-child** if every non-leaf vertex has a child that is a tree vertex or a leaf, and **normal** if it is tree-child and has no edge whose endpoints are also joined by another directed path. Let $T_{k,n}$ and $N_{k,n}$ count vertex-labelled tree-child and normal networks with $k$ reticulations and $n$ vertices, with exponential generating functions $T_k(z)$, $N_k(z)$, and let $\tilde T_{k,\ell}$, $\tilde N_{k,\ell}$ count leaf-labelled ones with $\ell$ leaves.

**Theorem (generating functions).** For $k = 1,2,3$ and $\star \in \{T, N\}$,

$$\star_k(z) = z\,\frac{\tilde a_k^{[\star]}(z^2) - \tilde b_k^{[\star]}(z^2)\sqrt{1 - 2z^2}}{(1 - 2z^2)^{2k - 1/2}},$$

with $\tilde a_1^{[T]} = \tilde b_1^{[T]} = z$; $\tilde a_2^{[T]} = -z^4 + 8z^3$, $\tilde b_2^{[T]} = 8z^3$; $\tilde a_3^{[T]} = -35z^6 + 175z^5$, $\tilde b_3^{[T]} = 34z^6 + 175z^5$; and $\tilde a_1^{[N]} = 2 - 3z$, $\tilde b_1^{[N]} = 2 - z$; $\tilde a_2^{[N]} = 11z^4 - 66z^3 + 50z^2 - 8z$, $\tilde b_2^{[N]} = -28z^3 + 42z^2 - 8z$ (with corresponding degree-6 polynomials for $k = 3$). These correct the expressions for $k = 2, 3$ in the earlier asymptotic study, without changing its first-order asymptotics.

**Corollary (explicit formulas).** Extracting coefficients,

$$T_{k,2n+1} = (2n+1)!\Big(2^{-n}\binom{2n}{n}\tilde r_k^{[T]}(n) - 2^n\,\tilde p_k^{[T]}(n)\Big), \qquad \tilde T_{k,\ell} = \frac{\ell!}{(2\ell + 2k - 1)!}\,T_{k,\,2\ell + 2k - 1},$$

and likewise for normal networks, with $\tilde r_1^{[T]}(n) = n$, $\tilde p_1^{[T]}(n) = \tfrac12$, $\tilde r_2^{[T]}(n) = \frac{n(n-1)(n-2)(3n-1)}{3(2n-1)}$, $\tilde p_2^{[T]}(n) = \tfrac12(n-1)(n-2)$, and $\tilde r_1^{[N]}(n) = n + 2$, $\tilde p_1^{[N]}(n) = \tfrac32$, $\tilde r_2^{[N]}(n) = \frac{n(3n-7)(n^2+9n-4)}{3(2n-1)}$, $\tilde p_2^{[N]}(n) = \tfrac12(n+1)(3n-7)$. For one reticulation this gives

$$\tilde T_{1,\ell} = \ell!\Big(\frac{\ell}{2^\ell}\binom{2\ell}{\ell} - 2^{\ell - 1}\Big),$$

e.g. $\tilde T_{1,3} = 21$.

**Theorem (labelling).** A network with $\ell$ leaves and $f$ independent vertices and independent pairs of vertices has exactly $\ell!\,2^{-f}$ distinct leaf labellings; hence for any label-closed class $\mathcal{C}$, $|\mathcal{C}_\ell|/\ell!$ has a power of $2$ as denominator.

## Expansion

The generating functions come from a decomposition: colour every reticulation red, pick one incoming edge of each and colour its parent green, and delete the picked edges; the result is a vertex-labelled Motzkin tree (binary and unary vertices) with $k$ red and $k$ green unary vertices, the colored Motzkin skeleton. Contracting the paths between green vertices and their common ancestors gives a finite set of sparsened skeletons, and reversing the process with the symbolic method, starting from the generating function of tree-child Motzkin trees $M(z,y) = \frac{(1+yz)(1 - \sqrt{1 - 2z^2 - 4yz^3})}{z(1+2yz)}$, produces the square-root singularity at $z^2 = 1/2$ and the pole order $2k - \tfrac12$. Coefficient extraction uses $[z^n]\,z^m(1-2z)^{-\alpha} = 2^{n-m}\binom{n-m+\alpha-1}{n-m}$: the half-integer exponent gives the central-binomial part $\tilde r_k$ and the integer exponent the polynomial part $\tilde p_k$; the labelling theorem, whose $2^{-f}$ accounts for symmetric cherries and pairs, converts vertex labellings into leaf labellings. The explicit $k = 3$ tree-child formula reproduces every value previously obtained algorithmically by Cardona and Zhang.

## Sources

- Michael Fuchs, Bernhard Gittenberger, Marefatollah Mansouri, "Counting phylogenetic networks with few reticulation vertices: exact enumeration and corrections", Australasian Journal of Combinatorics 81 (2021), 257–282, <https://ajc.maths.uq.edu.au/v81.p257> (the journal assigns no DOI). Published version of arXiv:2006.15784, cited next; locators there refer to the arXiv version.
- Michael Fuchs, Bernhard Gittenberger, Marefatollah Mansouri, "Counting Phylogenetic Networks with Few Reticulation Vertices: Exact Enumeration and Corrections", arXiv:2006.15784 (2020), Section 1 (generating-function form and the two correction theorems for tree-child and normal networks), Section 2 (coefficient extraction and the two theorems giving $\tilde r_k$, $\tilde p_k$) and Appendix (labelling theorem and Corollary), <https://doi.org/10.48550/arXiv.2006.15784>.
