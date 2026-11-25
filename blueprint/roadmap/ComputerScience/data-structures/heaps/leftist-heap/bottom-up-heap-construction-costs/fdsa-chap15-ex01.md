# Multi-pass cost bound for equally sized heaps

Let $T$ be a set of trees with an invariant $I$ (a property of trees), a size $|t| \in \mathbb{N}$,
a merge operation $t_1, t_2 \mapsto t_1 \sqcup t_2$ and a merge cost $c(t_1, t_2) \in \mathbb{N}$.
For $m \in \mathbb{N}$ let $B(m) = 2 \lfloor \log_2 (m + 1) \rfloor + 1$. One adjacent merging pass
replaces a list $t_1, t_2, t_3, t_4, \dots$ by $t_1 \sqcup t_2, t_3 \sqcup t_4, \dots$ (a last
unpaired tree is kept as it is) and costs $c(t_1, t_2) + c(t_3, t_4) + \cdots$. The multi-pass
cost of a list is $0$ if the list has at most one tree, and otherwise the cost of one pass plus
the multi-pass cost of the resulting list; it is computed with at most as many passes as the
length of the original list (once this budget runs out the remaining cost counts as $0$), which
always suffices because each pass shortens a list of length at least $2$.

Let $n, k \in \mathbb{N}$ and let $L$ be a list of $2^k$ trees, each satisfying $I$ and of size
$n$. Assume that for all trees $a, b$: $|a \sqcup b| = |a| + |b|$; if $a$ and $b$ satisfy $I$ then
so does $a \sqcup b$; and if $a$ and $b$ satisfy $I$ and $|a| = |b| = m$ then $c(a, b) \le B(m)$.
Then the multi-pass cost of $L$ is at most

$$\sum_{i=1}^{k} 2^{k-i} \, B\bigl(2^{i-1} n\bigr).$$

## Sources

- T. Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof Assistant Approach*, ACM
  Books, 2025 (author's version of 27 July 2026: https://fdsa-book.net/), Section 15.4, inequality
  (15.2), stated there for leftist heaps.
