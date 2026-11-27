# Parameterized complexity of median and closest permutations under rearrangement distances

**Setting.** Model a unichromosomal genome on $n$ genes as a permutation $\pi = [\pi(0)\,\pi(1)\cdots\pi(n)\,\pi(n+1)]$ of $\{1,\dots,n\}$ framed by $\pi(0) = 0$ and $\pi(n+1) = n+1$. The rearrangement distances considered are the **swap** distance (exchange two elements), **block-interchange** distance (exchange two blocks), **short-block-move** distance (exchange two adjacent blocks of total length at most 3, i.e. a transposition $t(i,j,k)$ with $k-i\le3$: a skip or a hop), **transposition** distance (exchange two adjacent blocks) and **breakpoint** distance (number of adjacencies of one permutation absent from the other). Given input permutations $\pi^1,\dots,\pi^k$ and a metric $d_M$:

- MEDIAN asks for $\sigma$ minimizing $\sum_{i=1}^k d_M(\sigma, \pi^i)$ (the *median genome*);
- CLOSEST asks for $\sigma$ minimizing $\max_i d_M(\sigma, \pi^i)$ (the *closest genome*).

Both are natural targets for rearrangement-based ancestral genome reconstruction, where the number $k$ of genomes and the optimum value $d$ are typically small.

**Theorem (hardness for few genomes).** BLOCK-INTERCHANGE MEDIAN is NP-complete already for $k = 3$ input permutations, hence para-NP-hard parameterized by $k$ (as were transposition and breakpoint median). Moreover, $\sigma$ solves block-interchange median for $\pi^1,\pi^2,\pi^3$ if and only if the six-fold concatenation of $\sigma$ solves block-interchange closest for three concatenated inputs built from six copies of the $\pi^i$ in suitable orders, so BLOCK-INTERCHANGE CLOSEST is also NP-hard for three permutations. SHORT-BLOCK-MOVE CLOSEST PERMUTATION is NP-hard.

**Theorem (median kernels).** Parameterized by the optimum value $d$ of the median, $d$-SWAP, $d$-BREAKPOINT, $d$-BLOCK-INTERCHANGE, $d$-TRANSPOSITION and $d$-SHORT-BLOCK-MOVE MEDIAN all admit polynomial kernels.

**Theorem (closest).** $d$-SWAP, $d$-SHORT-BLOCK-MOVE and $d$-BLOCK-INTERCHANGE CLOSEST are solvable in time $O^*(d^{O(d)})$, i.e. are FPT in $d$; but none of the five closest problems admits a polynomial kernel parameterized by $d$ unless $\mathrm{NP} \subseteq \mathrm{coNP}/\mathrm{poly}$, inheriting this from CLOSEST STRING parameterized by $d$ and $n$.

## Expansion

The kernels rest on reduction rules: an adjacency present in every input permutation can be assumed present in some median for block-interchange and transposition distances (contract it into one element); for short-block-moves, a run of $6d+1$ consecutive columns that agree across all inputs can be shortened without changing the optimum; and with total budget $d$ only $O(d)$ positions can differ from the inputs, bounding the reduced instance size. The NP-completeness for three permutations follows Caprara's approach for reversal medians, via a cycle-maximization formulation in which $d_{\mathrm{BI}}(\sigma,\pi) = (n+1-c(G(\sigma,\pi)))/2$ with $c$ the number of cycles of the breakpoint graph. FPT algorithms for CLOSEST bound the search by the at most $d$ operations separating a solution from each input, while the kernel lower bounds come from CLOSEST STRING.

## Sources

- Luís Cunha, Ignasi Sau and Uéverton Souza, "On the complexity of the median and closest permutation problems", arXiv:2311.17224 (2023), Section 2 (rearrangement distances and the Closest String kernel lower bound), Section 3 (block-interchange median NP-completeness for three permutations, reduction lemmas and polynomial kernels for all five median problems) and Section 4 (median-to-closest reduction, short-block-move closest NP-hardness, FPT algorithms), Appendix B (definition of short-block-moves), Table 1, <https://doi.org/10.48550/arXiv.2311.17224>. Published version: Algorithms for Molecular Biology 19 (2024) 24, <https://doi.org/10.1186/s13015-024-00269-z>.
