# Memory safety implies noninterference for unreachable memory

**Corollary.** In the [memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md), let $s_1$, $s_{21}$ and $s_{22}$ be states and $c$ a command with
$\mathrm{vars}(c) \subseteq \mathrm{vars}(s_1)$, $\mathrm{ids}(s_1) \# \mathrm{blocks}(s_{21})$ and $\mathrm{ids}(s_1) \# \mathrm{blocks}(s_{22})$. Then exactly one of the following holds:

1. $[\![c]\!](s_1 \cup s_{21}) = [\![c]\!](s_1 \cup s_{22}) = \bot$;
2. $[\![c]\!](s_1 \cup s_{21}) = [\![c]\!](s_1 \cup s_{22}) = \mathrm{error}$;
3. there are a state $s'_1$ and permutations $\pi_1, \pi_2$ with $[\![c]\!](s_1 \cup s_{2i}) = \pi_i \cdot s'_1 \cup s_{2i}$ and $\mathrm{ids}(\pi_i \cdot s'_1) \# \mathrm{blocks}(s_{2i})$ for $i = 1, 2$.

Memory unreachable from $s_1$ is neither modified nor observed: its contents do not influence the outcome.

## Depends on

- [Syntax and semantics of the memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md)

## Proof depends on

- [Frame theorem for terminating runs of memory-safe programs](frame-theorem-for-terminating-runs.md)
- [Frame theorem for nonterminating runs of memory-safe programs](frame-theorem-for-nonterminating-runs.md)
- [Frame theorem for erroneous runs of memory-safe programs](frame-theorem-for-erroneous-runs.md)

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 3.2, Corollary 1 (noninterference).
