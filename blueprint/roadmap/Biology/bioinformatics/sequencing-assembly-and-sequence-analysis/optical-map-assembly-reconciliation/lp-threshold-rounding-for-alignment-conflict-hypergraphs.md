# LP threshold rounding for alignment-conflict hypergraphs

When several genome assemblies are aligned to an optical map, let $a_{i,p}$ denote the alignment of contig $p$ to optical molecule $i$. Four alignments $a_{i,p}, a_{i,q}, a_{j,p}, a_{j,q}$ (two contigs on two molecules) are in **conflict** if their relative orientations disagree or the inter-contig distance on molecule $i$ differs significantly from that on molecule $j$; in a conflict at least one alignment is false. The **conflict hypergraph** $H = (V, E)$ has one vertex per alignment, weighted by its confidence $w_v \ge 0$, and one hyperedge per conflicting quadruple, so $|e| \le 4$ for every $e \in E$. Discarding a minimum-confidence set of alignments that resolves every conflict is the minimum-weight vertex cover problem on $H$:

$$\min \sum_{v \in V} w_v x_v \quad \text{s.t.} \quad \sum_{v \in e} x_v \ge 1 \ \ \forall e \in E, \qquad x_v \in \{0,1\}.$$

**Theorem (4-approximation by threshold rounding).** Let $x^*$ be an optimal solution of the linear relaxation ($0 \le x_v \le 1$). Let $S = \{v : x^*_v \ge 1/4\}$, and let $C \subseteq S$ be obtained by scanning $S$ in decreasing order of $x^*_v$ and keeping a vertex only if it covers a hyperedge not yet covered. Then $C$ is a vertex cover of $H$ and $w(C) \le 4\, w(C^{\mathrm{opt}})$, where $C^{\mathrm{opt}}$ is a minimum-weight vertex cover.

## Expansion

Every hyperedge has at most four vertices whose LP values sum to at least $1$, so some vertex of the hyperedge has $x^*_v \ge 1/4$ and lies in $S$; the greedy scan keeps a vertex for each still-uncovered hyperedge, so $C$ covers $E$. The cost chain is

$$w(C^{\mathrm{opt}}) \ \ge\ \sum_{v \in V} w_v x^*_v \ \ge\ \sum_{v \in S} w_v x^*_v \ \ge\ \tfrac14 \sum_{v \in S} w_v \ \ge\ \tfrac14\, w(C),$$

using in turn that the LP is a relaxation, $S \subseteq V$ with nonnegative terms, $x^*_v \ge 1/4$ on $S$, and $C \subseteq S$. The same argument gives ratio $k$ for hypergraphs with edges of size at most $k$. In the reconciliation pipeline, small connected components of the conflict hypergraph (at most twenty vertices) are solved exactly by enumeration and the rounding is applied only to larger components.

## Sources

- W. Pan, S. I. Wanamaker, A. M. V. Ah-Fong, H. S. Judelson, S. Lonardi, "Novo&Stitch: accurate reconciliation of genome assemblies via optical maps", Bioinformatics (2018), Section 3.1.1 (conflict hypergraph, integer program, Theorem 1) and Section 3.1.2 (Definition 2, Theorem 3). <https://doi.org/10.1093/bioinformatics/bty255> (PMC6022655)
