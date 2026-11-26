# Longest run subsequence problem

**Motivation.** In reference-guided scaffolding, a contig of one assembly $X$ is split into equal-size bins, and each bin is mapped to its best-matching contig of a related assembly $Y$. Reading the bins in order gives a string $S$ over the alphabet $\Sigma$ of $Y$-contigs. Mapping errors and mutations make $S$ inconsistent (a $Y$-contig appears in scattered bins), and the most likely partition of $X$ is read off from a longest subsequence in which each $Y$-contig appears contiguously.

**Definitions.** For a string $S$ over $\Sigma$, an *$a$-run* is a substring consisting only of the symbol $a$. A *run subsequence* of $S$ is a subsequence that contains at most one run of each symbol $a\in\Sigma$. **Longest Run Subsequence (LRS):** given $S$ and an integer $k$, decide whether $S$ has a run subsequence of length $k$ (optimization: maximize the length).

**Facts.**
- An optimal run subsequence need not use any maximal run (all occurrences of a symbol) and may omit symbols entirely: for $S=abacaabbab$ an optimum is $R=aaaabbb$, which uses no $c$ and neither all $a$'s nor all $b$'s.
- LRS is NP-hard and fixed-parameter tractable in $|\Sigma|$ (Schrinner et al., 2020).
- LRS has a kernel with $k^2$ symbols for the parameter $k$: if some symbol occurs at least $k$ times its run alone is a solution, and if $|\Sigma|\ge k$ one occurrence of each of $k$ symbols is a solution, so otherwise $|S|<k^2$.

## Expansion

Choosing a run of $a$ amounts to choosing an interval of $S$ and keeping all occurrences of $a$ inside it; the difficulty is that the chosen intervals for different symbols must appear in a consistent left-to-right order without interleaving, which is what makes the problem combinatorially hard despite being a subsequence problem. The kernel argument is a direct pigeonhole bound: a yes-instance is detected immediately unless every symbol occurs fewer than $k$ times and fewer than $k$ symbols occur.

## Sources

- R. Dondi, F. Sikora, "The longest run subsequence problem: further complexity results", 32nd Annual Symposium on Combinatorial Pattern Matching (CPM 2021); arXiv:2011.08119, <https://doi.org/10.48550/arXiv.2011.08119>. Sections 1 and 2 (problem definition, the example of non-maximal optimal runs, and the observation that LRS has a $k^2$ kernel).
