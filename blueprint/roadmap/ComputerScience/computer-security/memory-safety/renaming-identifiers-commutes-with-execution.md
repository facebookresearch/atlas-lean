# Renaming block identifiers commutes with execution

**Theorem (renaming states).** In the [memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md), for every state $s$, command $c$ and permutation $\pi$ of identifiers
there is a permutation $\pi'$ such that $[\![c]\!](\pi \cdot s) = \mathrm{error}$ if $[\![c]\!](s) = \mathrm{error}$, $[\![c]\!](\pi \cdot s) = \bot$ if $[\![c]\!](s) = \bot$, and
$[\![c]\!](\pi \cdot s) = \pi' \cdot \pi \cdot s'$ if $[\![c]\!](s) = s'$. Programs cannot observe identifiers, so renaming the initial state only changes the choice of fresh identifiers.

## Depends on

- [Syntax and semantics of the memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md)

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 3.1, Theorem 2 (renaming states).
