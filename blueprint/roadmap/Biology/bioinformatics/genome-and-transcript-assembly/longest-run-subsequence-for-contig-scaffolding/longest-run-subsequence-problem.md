# Longest run subsequence problem

**Motivation.** In reference-guided scaffolding, a contig of one assembly $X$ is split into equal-size bins, and each bin is mapped to its best-matching contig of a related assembly $Y$. Reading the bins in order gives a string $S$ over the alphabet $\Sigma$ of $Y$-contigs. Mapping errors and mutations make $S$ inconsistent (a $Y$-contig appears in scattered bins), and the most likely partition of $X$ is read off from a longest subsequence in which each $Y$-contig appears contiguously.

**Definitions.** For a string $R$ over $\Sigma$, an *$a$-run* of $R$ is a maximal substring of $R$ consisting only of the symbol $a$ (a maximal constant block). A *run subsequence* of $S$ is a subsequence $R$ of $S$ such that, for each symbol $a\in\Sigma$, all occurrences of $a$ **in $R$** form one contiguous block, equivalently $R$ has at most one $a$-run. The condition is on the chosen subsequence $R$, not on $S$: $R$ need not retain every occurrence of $a$ in $S$, and for instance $R=aa$ is a run subsequence of length 2 with one run (its substring $a$ is not a separate run, since it is not maximal). **Longest Run Subsequence (LRS):** given $S$ and an integer $k$, decide whether $S$ has a run subsequence of length $k$ (optimization: maximize the length).

**Facts.**
- An optimal run subsequence need not retain all occurrences of any symbol of $S$ and may omit symbols entirely: for $S=abacaabbab$ an optimum is $R=aaaabbb$, which uses no $c$ and neither all $a$'s nor all $b$'s.
- LRS is NP-hard and fixed-parameter tractable in $|\Sigma|$ (Schrinner et al., 2020).
- LRS has a kernel with $k^2$ symbols for the parameter $k$: if some symbol occurs at least $k$ times its run alone is a solution, and if $|\Sigma|\ge k$ one occurrence of each of $k$ symbols is a solution, so otherwise $|S|<k^2$.

## Expansion

Choosing a run of $a$ amounts to choosing an interval of $S$ and keeping all occurrences of $a$ inside it; the difficulty is that the chosen intervals for different symbols must appear in a consistent left-to-right order without interleaving, which is what makes the problem combinatorially hard despite being a subsequence problem. The kernel argument is a direct pigeonhole bound: a yes-instance is detected immediately unless every symbol occurs fewer than $k$ times and fewer than $k$ symbols occur.

## Sources

- R. Dondi, F. Sikora, "The longest run subsequence problem: further complexity results", 32nd Annual Symposium on Combinatorial Pattern Matching (CPM 2021); arXiv:2011.08119, <https://doi.org/10.48550/arXiv.2011.08119>. Sections 1 and 2 (problem definition, the example of non-maximal optimal runs, and the observation that LRS has a $k^2$ kernel).
