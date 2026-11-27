# Complexity of haplotype-aware sequence-to-graph alignment

**Haplotype-aware pangenome graph.** Let $G(V,E,\sigma,H)$ be a weakly connected DAG with $|E| \ge |V| - 1$, vertex labels $\sigma : V \to \Sigma$, and haplotypes $H = \{H_1,\dots,H_{|H|}\}$, each a path in $G$. Let $\mathrm{haps}(v) = \{i : H_i \ni v\}$, and assume $\mathrm{haps}(v) \ne \emptyset$ for every vertex and $\mathrm{haps}(u) \cap \mathrm{haps}(v) \ne \emptyset$ for every edge $(u,v)$. An *alignment path* is a sequence $P = (w_1,\dots,w_l)$ of pairs $w_i = (v_i, h_i)$ with $h_i \in \mathrm{haps}(v_i)$ and $(v_i, v_{i+1}) \in E$; a *recombination* occurs between $w_i$ and $w_{i+1}$ when $h_i \ne h_{i+1}$. Write $s(P)$ for the spelled string and $r(P)$ for the number of recombinations. For a query $Q \in \Sigma^+$ and threshold $k$:

- **Problem 1** (exact matching, limited recombinations): is there $P$ with $\mathrm{EDIT}(s(P),Q) = 0$ and $r(P) < k$?
- **Problem 2** (approximate matching, no recombination): is there $P$ with $\mathrm{EDIT}(s(P),Q) < k$ and $r(P) = 0$?
- **Problem 3** (approximate matching, limited recombinations): for costs $c_1, c_2 \ge 0$, is there $P$ with $c_1\,\mathrm{EDIT}(s(P),Q) + c_2\, r(P) < k$?

**Lemma 2 (algorithm).** Problems 1–3 can be solved in $O(|Q|\,|E|\,|H|)$ time.

**Lemma 3 (conditional lower bound).** For every constant $\epsilon > 0$ there is no algorithm solving Problem 2 or Problem 3 in time

$$O\big(|Q|^{1-\epsilon}|E||H| + |Q||E|^{1-\epsilon}|H| + |Q||E||H|^{1-\epsilon}\big)$$

unless the Strong Exponential Time Hypothesis (SETH) is false.

## Depends on

- [Li–Stephens haplotype copying model](../../../population-structure/li-stephens-haplotype-copying-model/README.md)
- [Sequence alignment](../../sequence-alignment/README.md)

## Expansion

The algorithm extends sequence-to-DAG alignment with a haplotype coordinate. Add a source $v_\epsilon$ with edges to all vertices; let $D(i,v,h)$ be the minimum cost of aligning the prefix $Q[1..i]$ to an alignment path ending at $(v,h)$, and $D''(i,v) = \min_{h \in \mathrm{haps}(v)} D(i,v,h)$. Then

$$D(i,v,h) = \min\Big( D(i-1,v,h) + c_1,\ \min_{(u,v)\in E,\ h \in \mathrm{haps}(u)} \big\{ D(i,u,h) + c_1,\ D(i-1,u,h) + c_1\,\mathrm{EDIT}(\sigma(v), Q[i]) \big\},$$

$$\qquad \min_{(u,v)\in E} \big\{ D''(i,u) + c_1 + c_2,\ D''(i-1,u) + c_1\,\mathrm{EDIT}(\sigma(v),Q[i]) + c_2 \big\} \Big),$$

covering insertion, deletion, match or mismatch along the same haplotype, and the same moves with a haplotype switch at cost $c_2$; keeping $D''$ makes each edge cost $O(|H|)$ per query position. The lower bound reduces Orthogonal Vectors: the Backurs–Indyk gadgets encode one vector set as $n$ query strings and the other as $n$ equal-length haplotypes threaded through a layered DAG with three vertices per layer, so that a recombination-free path within edit distance $\beta_1 n$ of some query exists iff an orthogonal pair exists.

## Sources

- G. Chandra, D. Gibney, C. Jain, "Haplotype-aware sequence alignment to pangenome graphs", Genome Research 34(9) (2024) 1265–1275, Methods (haplotype-aware pangenome graph; Problems 1–3; Lemmas 1–3), <https://doi.org/10.1101/gr.279143.124>, PMCID PMC11529843.
