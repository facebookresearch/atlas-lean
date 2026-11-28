# Parameterized and approximation complexity of longest run subsequence

**Problem.** Longest Run Subsequence (LRS): given a string $S$ over alphabet $\Sigma$ and an integer $k$, find a subsequence $R$ of $S$ of length $k$ in which, for each symbol, all occurrences of that symbol in $R$ form one contiguous block (equivalently, $R$ has at most one maximal constant block per symbol; occurrences of a symbol in $S$ may be dropped). Let $r$ be the number of maximal runs of $R$, so $r\le|\Sigma|$. 2-LRS is the restriction where every symbol occurs at most twice in $S$.

**Theorem.**
1. (FPT in the number of runs) LRS can be solved by a randomized algorithm in $O(2^r\,r\,|S|^3)$ time and polynomial space.
2. (No polynomial kernel) LRS has no polynomial kernel for the parameter $|\Sigma|$, and hence none for the parameter $r$, unless $\mathrm{NP}\subseteq\mathrm{coNP/poly}$.
3. (Inapproximability) 2-LRS is APX-hard, so LRS has no PTAS unless $\mathrm{P}=\mathrm{NP}$, even when each symbol occurs at most twice.

## Depends on

- [Longest run subsequence problem](longest-run-subsequence-problem.md)

## Expansion

For item 1, build an arithmetic circuit with one variable $x_a$ per symbol whose polynomial $P_{i,l,h}$ sums, by dynamic programming over prefixes $S[1..i]$, monomials recording which symbols' runs were used by run subsequences of length $h$ with $l$ runs; a run subsequence of length $h$ with $l$ runs over $a_1,\dots,a_l$ exists iff $x_{a_1}\cdots x_{a_l}$ is a multilinear monomial of $P$. Koutis–Williams multilinear monomial detection decides this in $O(2^r r|S|^2)$ time, and iterating over $k$ gives the bound. Item 2 is an OR-cross-composition from an NP-hard problem into LRS parameterized by $|\Sigma|$, combined with the Bodlaender–Jansen–Kratsch framework; since $r\le|\Sigma|$, the parameter $r$ inherits it. Item 3 is an L-reduction from Maximum Independent Set on cubic graphs: each vertex and edge becomes a block of symbols separated by separation substrings, a canonical solution keeps all separators, and an independent set of size $q$ corresponds to a run subsequence of length $5q+4(n-q)+3m+3(n+m)$.

## Sources

- R. Dondi, F. Sikora, "The longest run subsequence problem: further complexity results", 32nd Annual Symposium on Combinatorial Pattern Matching (CPM 2021); arXiv:2011.08119, <https://doi.org/10.48550/arXiv.2011.08119>. Section 3 (multilinear-monomial lemma and the randomized $O(2^r r|S|^3)$ theorem), Section 4 (no-polynomial-kernel theorem and corollary) and Section 5 (APX-hardness of 2-LRS and its supporting lemmas).
