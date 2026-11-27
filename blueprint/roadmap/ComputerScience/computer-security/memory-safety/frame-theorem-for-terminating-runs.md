# Frame theorem for terminating runs of memory-safe programs

**Theorem (Frame OK).** In the [memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md), let $c$ be a command and $s_1$, $s'_1$, $s_2$ states with
$[\![c]\!](s_1) = s'_1$, $\mathrm{vars}(c) \subseteq \mathrm{vars}(s_1)$ and $\mathrm{blocks}(s_1) \cap \mathrm{blocks}(s_2) = \emptyset$. Then there is a permutation $\pi$ of identifiers such that
$[\![c]\!](s_1 \cup s_2) = \pi \cdot s'_1 \cup s_2$ and $\mathrm{blocks}(\pi \cdot s'_1) \cap \mathrm{blocks}(s_2) = \emptyset$.

The extra state $s_2$ is untouched, and the result differs from $s'_1$ only by renaming the identifiers of blocks allocated by $c$.

## Depends on

- [Syntax and semantics of the memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md)

## Proof depends on

- [Renaming block identifiers commutes with execution](renaming-identifiers-commutes-with-execution.md)

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 3.1, Theorem 1 (Frame OK), with Theorem 2 (renaming states) used in its proof.
