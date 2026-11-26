# Path-unique de Bruijn subgraphs and minimal full-capacity label sets

**Labeling capacity.** In fluorescent labeling of DNA molecules, short probes (labels) bind to occurrences of fixed words, and imaging reports only where labels sit, not the underlying sequence. Model a label set as $\mathcal{A} = \{\mathbf{a}_1,\dots,\mathbf{a}_t\} \subseteq [q]^{d+1}$. For $\mathbf{x} \in [q]^n$, the labeling sequence $L_{\mathcal{A}}(\mathbf{x}) \in [0,t]^n$ records at position $j$ the index $i$ if $(x_j,\dots,x_{j+d}) = \mathbf{a}_i$ and $0$ otherwise. The **labeling capacity** is

$$\mathrm{cap}(\mathcal{A}) = \limsup_{n\to\infty}\frac{\log_2\big|\{L_{\mathcal{A}}(\mathbf{x}) : \mathbf{x}\in[q]^n\}\big|}{n} \le \log_2 q,$$

and $\mathcal{A}$ has *full capacity* if equality holds, meaning that asymptotically the labeling pattern carries as much information as the sequence itself. Let $s(q,d+1)$ be the minimum size of a full-capacity label set of length $d+1$.

**De Bruijn reformulation.** The de Bruijn graph $\mathcal{B}_{q,d}$ has vertex set $[q]^d$ and an edge $(a_1,\dots,a_d) \to (a_2,\dots,a_{d+1})$ for each word $(a_1,\dots,a_{d+1}) \in [q]^{d+1}$. A digraph is **path-unique** if for every $k \ge 1$ and every pair of vertices there is at most one walk of length $k$ between them. Deleting the edges of $\mathcal{A}$ from $\mathcal{B}_{q,d}$ leaves a path-unique digraph if and only if $\mathcal{A}$ has full capacity; hence, with $\gamma(q,d)$ the maximum number of edges of a path-unique subgraph of $\mathcal{B}_{q,d}$,

$$s(q,d+1) + \gamma(q,d) = q^{d+1}.$$

**Theorem.** A subgraph of $\mathcal{B}_{q,d}$ is *ordered $(d+1)$-partite* if its vertices split into $V_0,\dots,V_d$ with every edge going from some $V_i$ to some $V_j$ with $i < j$. Every ordered $(d+1)$-partite subgraph is path-unique, and every path-unique subgraph can be made ordered $(d+1)$-partite by deleting at most $2q^{d + d/(d+1)} = o(q^{d+1})$ edges. Consequently, with $M(q,d)$ the maximum number of edges of an ordered $(d+1)$-partite subgraph, $M(q,d) \le \gamma(q,d) \le M(q,d) + 2q^{d+d/(d+1)}$, and for fixed $d$

$$\frac{d-1}{d+1} \le \lim_{q\to\infty}\frac{\gamma(q,d)}{q^{d+1}} \le \frac{d}{d+1} - \frac{3}{4d(d+1)} \quad (d \ge 3), \qquad 0.448 < \lim_{q\to\infty}\frac{\gamma(q,2)}{q^3} \le \frac59.$$

Equivalently, the smallest full-capacity label sets of length $d+1$ over $q$ letters contain asymptotically between $\big(\frac{1}{d+1} + \frac{3}{4d(d+1)}\big)q^{d+1}$ and $\frac{2}{d+1}q^{d+1}$ labels (for $d \ge 3$), improving the earlier bounds $\frac12 - \frac{1}{(d+1)!} \le \lim \gamma/q^{d+1} \le \min\{1 - \frac{1}{d+1}, 1 - \frac{3}{4d}\}$.

## Expansion

If the unlabeled part of the de Bruijn graph had two distinct walks of the same length between two vertices, the two corresponding sequences would produce the same labeling pattern, and iterating such ambiguities creates exponentially many sequences per pattern, which costs capacity; path-uniqueness is exactly the absence of such ambiguities. An ordered partition forces every walk to climb through the levels, so walks have length at most $d$ and are determined by their endpoints in a $d$-dimensional de Bruijn graph. Conversely, a counting argument on walks of length $d+1$ in a path-unique subgraph shows that only $o(q^{d+1})$ edges can lie in cycles of the level structure. The bounds then come from optimizing the sizes of the levels: the lower bound from an explicit construction, and the upper bounds from weighted counting, using for $d = 2$ the Motzkin–Straus maximum of $\sum_i x_i x_{i+1}$ over the simplex.

## Sources

- Jiacheng Cao, Xin Wei and Xiande Zhang, "On the bounds of path-unique subgraph of De Bruijn graph", arXiv:2611.32249 (2026), Section 1 (Definitions 1.1–1.2, Theorem 1.1 quoting the labeling-capacity equivalence, Theorems 1.2–1.3), Section 3 (Definition 3.1, Lemmas 3.1–3.2, Theorem 3.1) and Section 4 (Lemmas 4.1–4.2, Theorem 4.1), <https://doi.org/10.48550/arXiv.2611.32249>.
