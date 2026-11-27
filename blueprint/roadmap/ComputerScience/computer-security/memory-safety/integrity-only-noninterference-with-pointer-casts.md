# Integrity-only noninterference when pointers can be cast to integers

Extend the [memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md) with an expression $\mathrm{cast}(e)$ that converts a pointer to an integer: for an arbitrary
fixed function $f : I \times \mathbb Z \to \mathbb Z$, it evaluates to $f([\![e]\!](s))$ when $[\![e]\!](s)$ is a pointer, so that identifiers become observable. The frame theorems and the secrecy part of noninterference then fail, but integrity survives.

**Theorem.** Let $s_1, s_2, s'$ be states and $c$ a command of the extended language with $\mathrm{vars}(c) \subseteq \mathrm{vars}(s_1)$, $\mathrm{ids}(s_1) \# \mathrm{blocks}(s_2)$ and
$[\![c]\!](s_1 \cup s_2) = s'$. Then $s' = s'_1 \cup s_2$ for some state $s'_1$ with $\mathrm{ids}(s'_1) \# \mathrm{blocks}(s_2)$: an unreachable region is left unchanged by any
terminating run, although its contents may now influence the rest of the result.

## Depends on

- [Syntax and semantics of the memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md)

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 4.2, Theorem 7 (integrity-only noninterference) and the discussion of pointer-to-integer casts before it.
