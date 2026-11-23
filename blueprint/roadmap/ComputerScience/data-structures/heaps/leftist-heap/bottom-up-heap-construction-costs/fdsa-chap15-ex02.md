# Cost bound for one adjacent merging pass

Let $T$ be a set of trees with an invariant $I$ (a property of trees), a size $|t| \in \mathbb{N}$
and a merge cost $c(t_1, t_2) \in \mathbb{N}$ for each pair of trees. For $m \in \mathbb{N}$ let
$B(m) = 2 \lfloor \log_2 (m + 1) \rfloor + 1$. The cost of one adjacent merging pass over a list
of trees is defined recursively: it is $0$ for the empty list and for a one-tree list, and for a
list $t_1, t_2$ followed by $L$ it is $c(t_1, t_2)$ plus the cost of the pass over $L$.

Let $n \in \mathbb{N}$ and let $L$ be a list of trees, each satisfying $I$ and of size $n$.
Suppose $c(t_1, t_2) \le B(n)$ for all trees $t_1, t_2$ satisfying $I$ with $|t_1| = |t_2| = n$.
Then the cost of one adjacent merging pass over $L$ is at most
$\lfloor \mathrm{len}(L) / 2 \rfloor \cdot B(n)$, where $\mathrm{len}(L)$ is the length of $L$.

## Sources

- T. Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof Assistant Approach*, ACM
  Books, 2025 (author's version of 27 July 2026: https://fdsa-book.net/), Section 15.4 (the bound on
  one pass of adjacent merging, stated there for leftist heaps).
