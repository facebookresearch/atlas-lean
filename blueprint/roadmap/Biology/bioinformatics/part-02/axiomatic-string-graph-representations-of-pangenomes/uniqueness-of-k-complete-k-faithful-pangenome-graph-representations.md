# Uniqueness of $k$-complete, $k$-faithful de Bruijn and variation graph representations

**Setting.** A *string graph* is $G=\langle V,E,l\rangle$ with directed edges $E\subseteq V^2$ and vertex labels $l:V\to\Sigma^+$. The labeling extends to paths by a map $\hat l$ that is *subpath-compatible*: each path $p$ induces an injection $\Psi_p:\mathrm{Int}(p)\to\mathrm{Int}(\hat l(p))$ with $\hat l(p[i..j])=\hat l(p)[\Psi_p(i,j)]$.

- In a **de Bruijn graph (dBG) of length $k$** every vertex carries a distinct $k$-mer, edges join vertices whose labels overlap in $k-1$ characters, and $\hat l$ concatenates labels with the overlaps removed, so $\Psi_p(i,j)=\langle i,j+k-1\rangle$.
- In a **variation graph (VG)** labels have arbitrary length and $\hat l(v_1\cdots v_m)=l(v_1)\cdots l(v_m)$.

Given strings $\mathcal S=\{S_1,\dots,S_n\}$, a pair $\langle G,\pi\rangle$ with $\pi:\mathcal S\to\{\text{paths of }G\}$ *represents* $\mathcal S$ if $\hat l(\pi(S_i))=S_i$ for all $i$ and every vertex and every edge of $G$ is used by some path $\pi(S_i)$.

- A common $k$-mer $S_i[p..p+k-1]=S_{i'}[p'..p'+k-1]$ is *reflected* if some common subpath $\pi(S_i)[q..q+m]=\pi(S_{i'})[q'..q'+m]$ has label intervals containing both occurrences. The representation is **$k$-complete** if every common $k$-mer of $\mathcal S$ is reflected.
- Two occurrences of one vertex $v$ are *directly $k$-extendable* if they extend to a common subpath of both string paths whose label has length $\ge k$, and *$k$-extendable* if they are joined by a chain of directly $k$-extendable occurrences of $v$. The representation is **$k$-faithful** if every pair of occurrences of every vertex is $k$-extendable.

So $k$-completeness says which fragments must be merged, and $k$-faithfulness says nothing else may be merged. Two representations are **equivalent** if they reflect exactly the same $m$-mers for every $m>0$.

**Theorem.** Let every $S_i$ have length $|S_i|\ge k$.

1. There is a representation of $\mathcal S$ by a de Bruijn graph of length $k$; it is unique up to isomorphism, and it is $k$-complete and $k$-faithful.
2. Any two $k$-complete and $k$-faithful variation-graph representations of $\mathcal S$ are equivalent.
3. Starting from the length-$k$ dBG of $\mathcal S$, the three local operations *Split*, *Merge* and *Collapse*, applied to consistent transition graphs, always terminate and yield a $k$-complete and $k$-faithful variation graph representing $\mathcal S$. In particular such a VG representation exists and is unique up to equivalence.

## Expansion

For the dBG the vertex set is forced to be the set of distinct $k$-mers in $\mathcal S$, so any label-preserving vertex bijection is an isomorphism. Unique labels give $k$-completeness, and since no label is shorter than $k$ every shared vertex is itself a common $k$-mer, which gives $k$-faithfulness.

For variation graphs the key lemma is that $k$-extendability transfers between $k$-complete representations. If two occurrences of a vertex of $G$ are $k$-extendable, then any vertex of $G'$ whose label interval overlaps the first occurrence also has an occurrence overlapping the second. Applied in both directions with $k$-faithfulness, this shows that $G$ and $G'$ merge exactly the same string positions, which means they reflect the same $m$-mers.

The constructive part rewrites the dBG, where each vertex spells $k$ characters, into a VG in which each position of each string is spelled exactly once. *Split* separates the $k$ characters of a vertex, *Merge* unifies vertices forced together by shared $(k-1)$-overlaps, and *Collapse* removes the redundancy. Each operation preserves consistency together with $k$-completeness and $k$-faithfulness. The result lets annotations and analyses move between the two pangenome models without loss.

The statements are the proposition of Section 2.3 (de Bruijn graphs), the equivalence lemma and theorem of Section 2.4 (variation graphs), the preservation lemmas of Sections 3.2–3.4 (Split, Merge, Collapse), and the correctness theorem with its corollary in Section 3.5 of the source.

## Sources

- A. Cicherski, N. Dojer, "From de Bruijn graphs to variation graphs – relationships between pangenome models", arXiv:2503.14520 (2025). <https://doi.org/10.48550/arXiv.2503.14520>
- Published version: A. Cicherski, N. Dojer, "From de Bruijn Graphs to Variation Graphs – Relationships Between Pangenome Models", String Processing and Information Retrieval (SPIRE 2023), Lecture Notes in Computer Science (2023), 114–128, <https://doi.org/10.1007/978-3-031-43980-3_10>.
