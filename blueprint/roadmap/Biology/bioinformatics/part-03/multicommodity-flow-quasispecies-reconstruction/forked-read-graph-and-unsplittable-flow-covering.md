# Forked read graph and unsplittable flow covering

An **amplicon** $A$ is a multiset of reads sharing start and end positions $\mathrm{start}(A) < \mathrm{end}(A)$ on the genome. Amplicons $A_1, \dots, A_m$ form an **overlapping set** if $\mathrm{start}(A_i) \le \mathrm{start}(A_{i+1}) < \mathrm{end}(A_i) \le \mathrm{end}(A_{i+1})$ for each $i$. For reads $r \in A_i$, $r' \in A_{i+1}$ write $r \prec r'$ if the suffix of $r$ of length $l_{i,i+1} = \mathrm{end}(A_i) - \mathrm{start}(A_{i+1}) + 1$ equals the prefix of $r'$ of that length. The **read graph** $G$ has a vertex for each distinct read of each amplicon (stage $V_i$), plus a source $s$ and sink $t$, edges $u \to v$ whenever $r_u \prec r_v$, edges $s \to V_1$ and $V_m \to t$, and vertex weights $c(v) \in [0,1]$ equal to the read's frequency within its amplicon. Every full-length variant with a read in each amplicon is an $(s,t)$-path. A **bipartite clique** is a set $C \subseteq V_i \cup V_{i+1}$ with every vertex of $C \cap V_i$ adjacent to every vertex of $C \cap V_{i+1}$.

**Lemma.** The consistency relation between consecutive amplicons $A_i, A_{i+1}$ partitions their edges into vertex-disjoint complete bipartite cliques of $G$.

**Forked read graph.** Replacing each $K_{p,q}$ clique by a new fork vertex with $p$ incoming and $q$ outgoing edges gives a $(2m+1)$-staged graph $H$ with $p + q$ instead of $pq$ edges per clique, edge demands $d(u\,v_{\mathrm{fork}}) = c(u)$, $d(v_{\mathrm{fork}}\,v) = c(v)$, $d = 0$ on source and sink edges, and the same $(s,t)$-paths.

**Covering problem.** With at most $k$ variants, flows $g^i$ and indicators $f^i$:

$$\min \sum_{i=1}^k \sum_{(s,u)} g^i_{su} \quad \text{s.t.} \quad \sum_{i} g^i_{uv} \ge d(uv), \quad \sum_{u} g^i_{uv} = \sum_{w} g^i_{vw}\ (v \ne s, t), \quad \sum_{u} f^i_{vu} \le 1, \quad f^i_{uv} \ge g^i_{uv}, \quad f^i_{uv} \in \{0,1\}, \ g^i_{uv} \in [0,1].$$

The out-degree constraint on $f^i$ makes each commodity an unsplittable flow along a single simple $(s,t)$-path $P_i$, and variant $i$ has estimated frequency $\sum_{(s,u)} g^i_{su} \big/ \sum_{j}\sum_{(s,u)} g^j_{su}$.

## Expansion

If two reads of $A_i$ shared a successor in $A_{i+1}$ but not all successors, their common successor's prefix would have to be consistent with both while another successor's prefix is not, contradicting that consistency only depends on the length-$l_{i,i+1}$ overlap string; hence the consistency relation is a disjoint union of complete bipartite blocks indexed by overlap strings. Forking these blocks shrinks the number of flow variables, which are attached to edges, from quadratic to linear per block. The mixed-integer program finds a minimum-total-frequency set of variants whose paths cover every observed read with at least its observed frequency (a covering formulation); a companion packing formulation for shotgun reads instead maximizes the number of reads explained by the most probable set of variants.

## Sources

- P. Skums, N. Mancuso, A. Artyomenko, B. Tork, I. Mandoiu, Y. Khudyakov, A. Zelikovsky, "Reconstruction of viral population structure from next-generation sequencing data using multicommodity flows", BMC Bioinformatics 14 (Suppl 9) (2013) S2, Methods ("AmpMCF algorithm"), Lemma 1, Problem 1 and Eqs. 1–9, <https://doi.org/10.1186/1471-2105-14-S9-S2>, PMCID PMC3698000.
