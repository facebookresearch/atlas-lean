# Rank queries and space of run-block compressed sequences

**Construction.** Let $T$ be a string of length $n$ over an alphabet of size $\sigma$ (in practice the Burrows–Wheeler transform of a genome collection), with $r$ maximal runs of equal characters and average run length $\ell = n/r$. Fix a block length $b$ and cut $T$ into $\lceil n/b \rceil$ consecutive blocks. A block is a *run block* if all its characters are equal. The run-block compressed representation consists of

- a bit vector $B_R$ of length $\lceil n/b\rceil$ marking run blocks;
- the string $T_R$ holding the single character of each run block, in order;
- the string $T_P$ concatenating the non-run blocks verbatim;

with $T_R$ and $T_P$ stored in wavelet trees and $B_R$ with constant-time binary rank. For $c$ a character and $1 \le i \le n$ let $\mathrm{rank}_c(i, T)$ count occurrences of $c$ in $T[1..i]$.

**Theorem (rank).** $\mathrm{rank}_c(i, T)$ can be computed in $O(\log \sigma)$ time. With $k = \lceil i/b \rceil$, $r_r = \mathrm{rank}_1(k, B_R)$ and $\bar r_r = k - r_r$, if block $k$ is a run block then

$$\mathrm{rank}_c(i, T) = b\,\mathrm{rank}_c(r_r, T_R) + \mathrm{rank}_c(\bar r_r b, T_P) + \mathbf 1[T_R[r_r] = c]\,\bigl((i-1) \bmod b + 1 - b\bigr),$$

and if it is not, the run-block part counts the $r_r$ preceding run blocks and the remainder is a rank query in $T_P$ at position $(\bar r_r - 1)b + (i-1) \bmod b + 1$.

**Theorem (space).** With $b$ chosen of order $\sqrt{n/r}$, the representation uses $O\!\left(\dfrac{n}{\sqrt{\ell}}\log\sigma\right)$ bits, sublinear in $n$ when runs are long.

## Depends on

- [Succinct rank and select](../../../../ComputerScience/data-structures/range-query-structures/advanced-data-structures/succinct-rank-and-select.md)

## Expansion

Each non-run block contains at least one run head, so there are at most $r$ non-run blocks; hence $|T_P| \le rb$ and $|T_R| \ge n/b - r$. With $A = O(\log\sigma)$ bits per wavelet-tree character the total is about $S(b) = A r b + (1 + A)\,n/b - A r$, minimized at $b \approx \sqrt{(1+A)n/(Ar)}$, giving $S = O(A\sqrt{nr}) = O(n\log\sigma/\sqrt{\ell})$. The rank formula decomposes the prefix into whole run blocks (each contributing $b$ copies of its character), whole non-run blocks, and the partial current block.

## Sources

- L. Song and B. Langmead, "Centrifuger: lossless compression of microbial genomes for efficient and accurate metagenomic sequence classification", *Genome Biology* (2024), Methods, run-block compression, Theorems 1 and 2. <https://doi.org/10.1186/s13059-024-03244-4> (PMC11046777)
