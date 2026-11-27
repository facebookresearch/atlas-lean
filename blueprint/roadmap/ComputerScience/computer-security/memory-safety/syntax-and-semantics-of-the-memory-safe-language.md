# Syntax and semantics of the memory-safe language

Let $I$ be a countably infinite set of *block identifiers*. *Values* are integers, booleans, the invalid pointer $\mathrm{nil}$ and pointers $(i, n) \in I \times \mathbb Z$ (a block and an
offset). A *state* $s = (l, m)$ is a local store $l$, a finite partial map from variables to values, and a heap $m$, a finite partial map from $I \times \mathbb Z$ to values;
outcomes are states and $\mathrm{error}$. Expressions are variables, constants, $\mathrm{nil}$, arithmetic, comparisons, boolean connectives and $\mathrm{offset}(e)$, and
evaluate totally: a variable not in $\mathrm{dom}(l)$ and an ill-typed operation give $\mathrm{nil}$, adding or subtracting an integer to a pointer changes only its offset,
equality of pointers compares block and offset, and $\mathrm{offset}((i, n)) = n$. Commands are

$$c ::= x \leftarrow e \mid x \leftarrow [e] \mid [e_1] \leftarrow e_2 \mid x \leftarrow \mathrm{alloc}(e) \mid \mathrm{free}(e) \mid \mathrm{skip} \mid \mathbf{if}\ e\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2 \mid \mathbf{while}\ e\ \mathbf{do}\ c\ \mathbf{end} \mid c_1; c_2,$$

with denotation $[\![c]\!](s)$ a state, $\mathrm{error}$, or $\bot$ for nontermination. Reading or writing through a pointer $p$ with $m(p)$ undefined gives $\mathrm{error}$;
$x \leftarrow \mathrm{alloc}(e)$ with $e$ evaluating to $n$ picks an identifier $i$ fresh for the whole state, sets $x$ to $(i, 0)$ and defines $(i, k) \mapsto 0$ for $0 \le k < n$; and
$\mathrm{free}(e)$, for $e$ evaluating to a pointer $(i, 0)$ with $i$ a live block ($m(i, n)$ defined for some $n$, not necessarily $n = 0$), makes every cell of block $i$
undefined (otherwise it gives $\mathrm{error}$). A guard of $\mathbf{if}$ or $\mathbf{while}$ that is not a boolean, an address in a read or a write that
is not a pointer, and an allocation size that is not an integer also give $\mathrm{error}$.

For the frame properties write $\mathrm{blocks}(l, m) = \{i \mid \exists n.\ (i, n) \in \mathrm{dom}(m)\}$ for the live blocks; $\mathrm{ids}(s)$ for the identifiers occurring anywhere in $s$
(live blocks and pointers stored in $l$ or $m$); $\mathrm{vars}(s) = \mathrm{dom}(l)$ and $\mathrm{vars}(c)$ for the local variables of $c$; $(l_1, m_1) \cup (l_2, m_2) = (l_1 \cup l_2, m_1 \cup m_2)$,
with $f \cup g$ taking $f(x)$ on $\mathrm{dom}(f)$ and $g(x)$ elsewhere; $X \# Y$ for disjointness; and $\pi \cdot s$ for renaming identifiers by a permutation $\pi$ of $I$.

## Sources

- A. Azevedo de Amorim, C. Hriţcu and B. C. Pierce, "The meaning of memory safety", *Principles of Security and Trust (POST 2018)*, arXiv:1705.07354v3, <https://arxiv.org/abs/1705.07354v3>: Section 2, Figure 1 and the Appendix, Figures 5–6 (syntax, states and values, errors, fresh and initialized allocation, opaque identifiers), Section 3.1, Figure 2 (notation), and the Appendix, Figures 3–6 (expression evaluation and the denotational semantics of commands).
