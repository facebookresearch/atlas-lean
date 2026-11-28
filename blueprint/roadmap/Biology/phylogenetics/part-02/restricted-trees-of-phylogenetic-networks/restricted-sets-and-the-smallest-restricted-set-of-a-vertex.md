# Restricted sets and the smallest restricted set of a vertex

Let $N=(V,A,r,X)$ be a rooted acyclic $X$-network: a directed graph without loops or multiple arcs, with root $r$ (every vertex is reachable from $r$), whose outdegree-0 vertices (leaves) are identified with the finite set $X$, and in which every vertex has a directed path to some leaf. Write $u \le v$ when there is a directed path from $u$ to $v$; this is a partial order on $V$.

A nonempty set $B \subseteq V$ with $r \notin B$ is **restricted** if there is a unique vertex $w' \notin B$ such that some arc $(w',b)$ has $b \in B$, and every arc $(w,b)$ with $w \notin B$, $b \in B$ has $w = w'$; this $w'$ is the **anchor** $\mathrm{Anc}(B)$. A set $B$ containing $r$ is restricted if no arc enters $B$ from outside. A set $B$ is **closed** if $b_1, b_2 \in B$ and $b_1 < v < b_2$ imply $v \in B$. Then:

1. Every restricted set is closed, and if $r \notin B$ then every $b \in B$ is reached from $\mathrm{Anc}(B)$ by a directed path all of whose vertices after the first lie in $B$ (Lemmas 3.1 and 3.2).
2. If $B$ and $C$ are restricted and $B \cap C \neq \emptyset$, then $B \cup C$ is restricted (Theorem 3.3). If $B$ and $C$ are restricted and some arc goes from $B$ to $C$, then $B \cup C$ is restricted (Lemma 3.4).
3. For $v \in V$ define $R(v)$ by the closure procedure: start with $R_0 = \{v\}$; given $R_i$, adjoin a vertex $u \notin R_i$ having an arc $(u,w)$ with $w \in R_i$ whenever either (a) $u \not\le w'$ for some $w' \in R_i$, or (b) there is an arc $(u',v')$ with $u' \notin R_i$, $u' \neq u$, $v' \in R_i$ and $u \not\le u'$; stop when no vertex can be adjoined. The result does not depend on the order of the additions, and:
   - $R(v)$ is restricted (Theorem 3.5);
   - every restricted set containing $v$ contains $R(v)$, so $R(v)$ is the smallest restricted set containing $v$ (Theorem 3.6), and $u \in R(v)$ implies $R(u) \subseteq R(v)$ (Corollary 3.7);
   - every $w \in R(v)$ has a directed path to $v$ inside $R(v)$, and $R(v)$ is connected in the underlying undirected graph (Lemma 3.8).

In particular a vertex $v$ of indegree 1 has $R(v) = \{v\}$, so in a rooted tree every singleton is restricted.

## Expansion

A restricted set is a bottleneck: everything entering it passes through its anchor, so in a successively cluster-distinct network it behaves like a single ancestral taxon. Closedness follows because a vertex strictly between two members with an arc into the set would be the anchor while also lying below a member, creating a directed cycle. For overlapping $B$ and $C$, following a path from $\mathrm{Anc}(B)$ into $B \cap C$ shows that $\mathrm{Anc}(B) \in C$, $\mathrm{Anc}(C) \in B$, or the anchors coincide; in each case one anchor serves the union. The closure procedure only adjoins vertices that any restricted set containing the current set must already contain (an outside entry vertex that is not below every member, or one of two distinct entry vertices, cannot be the anchor), which gives minimality; termination with no adjoinable vertex forces a unique entry vertex, which gives restrictedness.

## Sources

- Stephen J. Willson, Restricted trees: simplifying networks with bottlenecks, arXiv:1005.4956 (2010). <https://doi.org/10.48550/arXiv.1005.4956>. Published version: Bulletin of Mathematical Biology 73(10) (2011), 2322–2338, <https://doi.org/10.1007/s11538-010-9624-2>; locators above refer to the arXiv version.
