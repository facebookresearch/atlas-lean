# A memory-safe language with block identifiers

Values of the language are integers, pointers $(i, n)$ made of a block identifier $i$ from a set $I$ and an integer offset $n$, and $\mathrm{nil}$. A *state* $s = (l, m)$ is a
local store $l$, a partial map from variables to values, and a memory $m$, a partial map from pointers to values. Commands of an imperative language read and write
memory through pointers, allocate blocks and free them. Pointer arithmetic changes only offsets; an access through a pointer whose block is not live is an error;
allocation picks an identifier fresh for the whole state and initializes the block to $0$; identifiers cannot be inspected by programs, only offsets and pointer
equality. The semantics $[\![c]\!](s)$ of a command is a final state, $\mathrm{error}$, or $\bot$ for nontermination. With $\mathrm{blocks}(s)$ the identifiers of live blocks,
$\mathrm{ids}(s)$ all identifiers in the state, $\mathrm{vars}(s)$ the defined local variables, $s_1 \cup s_2$ the union of states and $\pi \cdot s$ the renaming of identifiers by a
permutation $\pi$ of $I$, frame properties describe how running $c$ on an extended state $s_1 \cup s_2$ relates to running it on $s_1$.

## Expansion

This node names a family of definitions. A good expansion adds a page for each of the following and links it under the dependency sections:

- Definition: syntax of expressions and commands and their denotational semantics (Section 2 and Figure 1 of the source).
- Definition: the notation of Figure 2 (union of states, $\mathrm{blocks}$, $\mathrm{ids}$, $\mathrm{vars}$ and renaming by permutations).

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 2 (the language, block identifiers as capabilities, freshness and initialization of allocated memory) and Section 3.1, Figure 2.
