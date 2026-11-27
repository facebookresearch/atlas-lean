# Frame theorem for nonterminating runs of memory-safe programs

**Theorem (Frame Loop).** In the [memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md), if $[\![c]\!](s_1) = \bot$, $\mathrm{vars}(c) \subseteq \mathrm{vars}(s_1)$ and
$\mathrm{blocks}(s_1) \cap \mathrm{blocks}(s_2) = \emptyset$, then $[\![c]\!](s_1 \cup s_2) = \bot$: extending the initial state cannot make a diverging program terminate.

## Depends on

- [Syntax and semantics of the memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md)

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 3.1, Theorem 3 (Frame Loop).
