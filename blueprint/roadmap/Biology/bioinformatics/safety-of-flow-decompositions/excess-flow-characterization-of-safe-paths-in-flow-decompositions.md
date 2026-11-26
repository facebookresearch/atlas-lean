# Excess-flow characterization of safe paths in flow decompositions

**Setting.** RNA transcript assembly reconstructs transcripts and their abundances by decomposing the flow on a splice graph. Let $G=(V,E)$ be a DAG with a positive flow $f(e)$ on every edge that is conserved at every vertex other than sources and sinks. For a vertex $u$, $f_{in}(u)$ and $f_{out}(u)$ are its total incoming and outgoing flow. A *flow decomposition* is a set of weighted source-to-sink paths whose weights add up to $f(e)$ on every edge $e$. A path $P$ is *$w$-safe* if in every flow decomposition $P$ is a subpath of decomposition paths of total weight at least $w$. It is *safe* if it is $w$-safe for some $w>0$, and *maximal safe* if no extension by one edge on either side is safe.

**Definition (excess flow).** For a path $P=(u_1,\dots,u_k)$,

$$f_P=f(u_1,u_2)-\sum_{\substack{u_i\in\{u_2,\dots,u_{k-1}\}\\ v\ne u_{i+1}}}f(u_i,v)=\sum_{i=1}^{k-1}f(u_i,u_{i+1})-\sum_{i=2}^{k-1}f_{out}(u_i).$$

By conservation of flow this equals the converging form $f(u_{k-1},u_k)-\sum_{u_i\in\{u_2,\dots,u_{k-1}\},\,v\ne u_{i-1}}f(v,u_i)$.

**Theorem.** For $w>0$, a path $P$ is $w$-safe if and only if $f_P\ge w$. In particular, $P$ is safe if and only if $f_P>0$.

**Lemma (incremental update).** Prepending an edge $(u,v)$ to a path that starts at $v$ lowers its excess flow by $f_{in}(v)-f(u,v)$. Appending an edge $(u,v)$ to a path that ends at $u$ lowers it by $f_{out}(u)-f(u,v)$.

So safety, which is defined by a quantifier over all decompositions, is a local quantity computable in $O(|P|)$ time after $O(m)$ preprocessing of vertex in- and out-flows.

## Expansion

At worst, all flow on edges that leave $P$ at internal vertices could have entered $P$ through its first edge. Whatever exceeds this maximum leakage must traverse all of $P$, so $P$ is $f_P$-safe. Conversely, if $f_P<w$, take any decomposition carrying more than $\max(f_P,0)$ weight along all of $P$. Some decomposition path enters $P$ after its first edge and leaves before its last edge, and it can be swapped with a path that traverses $P$: one new path enters at the first edge and leaves at the internal exit, the other enters at the internal entry and leaves at the last edge. Each swap reduces the weight on $P$ while preserving every edge flow, until only $f_P$ (or $0$) remains. The lemma follows directly from the two summation forms of $f_P$.

## Sources

- Shahbaz Khan, Milla Kortelainen, Manuel Cáceres, Lucia Williams, Alexandru I. Tomescu, "Safety and Completeness in Flow Decompositions for RNA Assembly", arXiv:2201.10372 (2022), Section 2 (preliminaries), Section 3 (Definition 1, Theorem 1, Lemma 1), <https://doi.org/10.48550/arXiv.2201.10372>.
