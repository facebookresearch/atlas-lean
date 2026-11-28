# Shortest common superstrings collapse long repeats

**Statement.** Let $S=\{s_1,\dots,s_m\}$ be a set of strings (reads), each of length $\ell$, and let $g$ be a shortest common superstring (SCS) of $S$. Then no string $r$ with $|r|>2\ell-2$ occurs in $g$ at two different locations. In other words, a shortest common superstring contains no repeat longer than $2\ell-2$.

**Consequence for assembly.** Real genomes contain repeats much longer than a read. Since the SCS of the reads never contains such a repeat, it can be strictly shorter than the true genome. So the SCS formulation of genome assembly is biologically wrong, even when solved exactly and not merely approximated by a greedy heuristic. This motivates spectrum-based formulations, in which the assembly must not introduce $k$-mers absent from the reads, and edge-covering walks in the de Bruijn graph. When repeats make the genome non-unique, it also motivates the shift to outputting only *safe* strings, those present in every solution, such as unitigs and omnitigs.

## Expansion

Suppose $g$ contains two occurrences of a repeat $r$ with $|r|>2\ell-2$. Write $r=xyz$ with $|x|=|z|=\ell-1$ and $|y|\ge1$. Form $g'$ by deleting $y$ from the second occurrence, which replaces it by $xz$. Every read whose occurrence in $g$ avoids the deleted $y$ is still a substring of $g'$. A read overlapping the deleted $y$ has length $\ell=|x|+1=|z|+1$, so it lies entirely within that occurrence of $xyz$. It therefore also lies within the first occurrence of $r$, which is untouched. Hence $g'$ is a common superstring strictly shorter than $g$, contradicting minimality.

This is the repeat theorem of the source's tutorial case study on modeling genome assembly.

## Sources

- P. Medvedev, "Modeling Biological Problems in Computer Science: A Case Study in Genome Assembly", arXiv:1706.05429 (2017). <https://doi.org/10.48550/arXiv.1706.05429>
