# Link-cut trees take logarithmic amortized time

A [link-cut tree](access.md) represents a forest of rooted trees on $n$ vertices under the operations $\mathrm{link}(v, w)$, which makes the root $v$ a child of $w$ in another tree, $\mathrm{cut}(v)$, $\mathrm{find\text{-}root}(v)$, and aggregates over root-to-vertex paths.
- Each vertex has at most one *preferred child*: the child whose subtree contains the most recent access in its own subtree.
- The preferred edges partition the forest into *preferred paths*. Each preferred path is stored as a splay tree keyed by depth.
- Every operation is reduced to $\mathrm{access}(v)$. This makes the root-to-$v$ path preferred by walking up and switching preferred children, splaying at each step.

**Theorem (Sleator–Tarjan).** Every link-cut tree operation takes $O(\log n)$ amortized time.

**Proof.**
1. *Preferred-child changes.* Call the edge to a child $v$ *heavy* if $\mathrm{size}(v) > \mathrm{size}(\mathrm{parent}(v))/2$, and *light* otherwise. Each vertex has at most one heavy child edge, and every root-to-vertex path has at most $\log_2 n$ light edges. An access makes at most $\log_2 n$ light edges preferred. A heavy edge becomes unpreferred only when a light edge beside it becomes preferred, at the end of an access, or when a link or cut changes subtree sizes, which affects $O(\log n)$ edges on one path. So over $m$ operations, heavy edges become preferred $O(m\log n + n)$ times. The number of preferred-child changes is therefore $O(\log n)$ amortized per operation, once $m \ge n$.
2. *Cost of the splays.* Use the potential $\Phi = \sum_v \log_2 s(v)$, where $s(v)$ is the size of $v$'s subtree in the tree of auxiliary splay trees. By the access lemma for splay trees, splaying $v$ within its auxiliary tree costs at most $3(\log s(\text{aux root}) - \log s(v)) + 1$. Along one access these bounds telescope to $3\log_2 n + O(\#\text{preferred-child changes}) = O(\log n)$.
3. A cut only decreases sizes. A link increases the potential by at most $\log_2 n$.

## Depends on

- [Access in a link-cut tree](access.md)

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 19 "Dynamic graphs I: link-cut trees" (scribe notes, Spring 2012), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec19.pdf>:
    - Section 2: the link-cut tree operations, all in $O(\lg n)$ amortized time;
    - Section 3: preferred children and paths, auxiliary splay trees keyed by depth, and access;
    - Section 4.1: the heavy-light decomposition (heavy when $\mathrm{size}(v) > \tfrac12\mathrm{size}(\mathrm{parent}(v))$, light depth at most $\lg n$) and $O(\lg n)$ amortized preferred-child changes;
    - Section 4.2: the potential $\sum_v \lg s(v)$, the access theorem, the telescoping sum, and the potential change under link and cut.
