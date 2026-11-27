# A memory-safe language with block identifiers

Values of the language are integers, Booleans, the invalid pointer $\mathrm{nil}$ and pointers $(i, n)$ made of a block identifier $i$ from a countably infinite set $I$ and
an integer offset $n$. A *state* $s = (l, m)$ is a local store $l$, a finite partial map from variables to values, and a heap $m$, a finite partial map from pointers
$I \times \mathbb{Z}$ to values. Commands of an imperative language read and write
memory through pointers, allocate blocks and free them. Pointer arithmetic changes only offsets; reading or writing through a pointer $p$ with $m(p)$ undefined is an error (a live block need not make every offset valid), and freeing
needs a pointer $(i, 0)$ to a live block $i$, one with $m(i, n)$ defined for some $n$;
allocation picks an identifier fresh for the whole state and initializes the block to $0$; identifiers cannot be inspected by programs, only offsets and pointer
equality. The semantics $[\![c]\!](s)$ of a command is a final state, $\mathrm{error}$, or $\bot$ for nontermination. With $\mathrm{blocks}(l, m) = \{i \mid \exists n.\ (i, n) \in \mathrm{dom}(m)\}$ the identifiers of live blocks, $\mathrm{ids}(s)$ all identifiers in the state (live blocks and
pointers stored in $l$ or $m$), $\mathrm{vars}(s) = \mathrm{dom}(l)$ the defined local variables, $\mathrm{vars}(c)$ the local variables of a command $c$, the componentwise
*left-biased* union $(l_1, m_1) \cup (l_2, m_2) = (l_1 \cup l_2, m_1 \cup m_2)$, where $(f \cup g)(x) = f(x)$ for $x \in \mathrm{dom}(f)$ and $g(x)$ otherwise, and $\pi \cdot s$ the
renaming of identifiers by a permutation $\pi$ of $I$, frame properties describe how running $c$ on an extended state $s_1 \cup s_2$ relates to running it on $s_1$.

## Expansion

This node names a family of definitions. A good expansion adds a page for each of the following and links it under the dependency sections:

- Definition: syntax of expressions and commands and their denotational semantics (Section 2 and Figure 1 of the source); stated, with the notation below, in [Syntax and semantics of the memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md).
- Definition: the notation of Figure 2 (union of states, $\mathrm{blocks}$, $\mathrm{ids}$, $\mathrm{vars}$ and renaming by permutations).

## Depends on

- [Syntax and semantics of the memory-safe language](syntax-and-semantics-of-the-memory-safe-language.md)

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 2 and Figure 1 (the language, values, states, errors, block identifiers as capabilities, freshness and initialization of allocated memory) Section 3.1, Figure 2 (notation, including the left-biased union of partial functions), and Appendix Figure 6 (the rule for $\mathrm{free}(e)$ on a sparse live block).
