# Frame theorem for erroneous runs of memory-safe programs

**Theorem (Frame Error).** In the [memory-safe language](block-structured-memory-safe-language.md), if $[\![c]\!](s_1) = \mathrm{error}$, $\mathrm{vars}(c) \subseteq \mathrm{vars}(s_1)$ and
$\mathrm{ids}(s_1) \cap \mathrm{blocks}(s_2) = \emptyset$, then $[\![c]\!](s_1 \cup s_2) = \mathrm{error}$.

The stronger premise, on all identifiers of $s_1$ rather than its live blocks, prevents a dangling pointer of $s_1$ from becoming valid in the extended state;
it is useful because programs cannot forge pointers to existing blocks.

## Depends on

- [A memory-safe language with block identifiers](block-structured-memory-safe-language.md)

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 3.1, Theorem 4 (Frame Error) and the discussion preceding it.
