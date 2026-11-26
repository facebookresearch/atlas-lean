# Ancestors by interval nesting

In the [depth-first search of the whole graph](dfs-all.md) of a directed graph, $u$ is an
ancestor of $v$ in the
depth-first forest if and only if

$$\mathrm{pre}(u) \le \mathrm{pre}(v) \quad\text{and}\quad \mathrm{post}(v) \le \mathrm{post}(u),$$

where $\mathrm{pre}$ and $\mathrm{post}$ are the indices in discovery order (preorder) and in
finishing order (postorder). With a single clock this is Erickson's condition
$u.\mathrm{pre} \le v.\mathrm{pre} < v.\mathrm{post} \le u.\mathrm{post}$: the active interval of
$u$ contains that of $v$.

The converse direction rests on an invariant of the search machine: if $u$ is discovered before
$v$ and is not an ancestor of $v$, then $u$ has finished when $v$ is discovered, hence before $v$
finishes.

## Sources

- J. Erickson, *Algorithms* (1st ed., 2019), Chapter 6, Lemma 6.1, (a) ⇔ (b).
