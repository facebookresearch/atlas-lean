# Max-flow bounds on good flow over all flow decompositions

**Setting.** Let $G=(V,E)$ be a DAG with source $S$ and sink $T$, and let $F=\{f_e\}$ be a flow: nonnegative edge weights balanced at every vertex other than $S,T$, with total value $U$. A *decomposition* of $F$ is a finite family $R=\{(T_i,c_i)\}$ of $S$–$T$ paths with weights $c_i\ge0$ such that $\sum_{i:\,e\in T_i}c_i=f_e$ for every edge. Every flow on a finite graph has one. For $E'\subseteq E$, a path is *good* if it meets $E'$, and the good flow of $R$ is $Q(R)=\sum_{i:\,T_i\cap E'\ne\emptyset}c_i$. The problem $\mathrm{OR\text{-}Quant}(G,E')$ asks for $\min_R Q(R)$ and $\max_R Q(R)$.

**Theorem.** Let $G^-$ be $G$ with the edges of $E'$ deleted, and let $G^+$ be $G$ with a new sink $T'$ to which the head of every edge of $E'$ is redirected. Both carry the capacities $f_e$. Then

$$\mathrm{OR\text{-}Quant}(G,E')=\bigl[\,U-\mathrm{MaxFlow}(G^-),\ \mathrm{MaxFlow}(G^+)\,\bigr].$$

Constructing $G^\pm$ takes linear time, so the cost is that of two maximum-flow computations. In transcript quantification, $f$ is the inferred splice-graph flow, and the interval is the range of total abundance of transcripts that use at least one junction of $E'$, over all equally likely sets of transcripts explaining $f$.

## Expansion

*Lower bound.* Bad paths are exactly the $S$–$T$ paths of $G^-$, so the bad part of any decomposition is a flow in $G^-$, giving $Q(R)\ge U-\mathrm{MaxFlow}(G^-)$. Conversely, decompose a maximum flow of $G^-$ and the remainder $F-F^-$ separately. If the remainder contained a bad path, moving it into the $G^-$ part would exceed the maximum, so the bound is attained.

*Upper bound.* Truncating each good path at its first edge in $E'$ maps the good part of any decomposition to a flow in $G^+$, so $Q(R)\le\mathrm{MaxFlow}(G^+)$. Attainment is constructive: decompose a maximum flow of $G^+$ into truncated paths. Repeatedly take the one whose last vertex before $T'$ is latest in topological order, and complete it from the head $v$ of its redirected edge by a $v$–$T$ flow of the same weight inside the residual of $F$. An induction on the number of paths shows that the capacities are never exceeded and every completed path stays good.

## Sources

- H. Zheng, C. Ma, C. Kingsford, "Deriving ranges of optimal estimated transcript expression due to nonidentifiability", *Journal of Computational Biology* 29(2):121–139 (2022), Section 2.4.1, Definitions 2–6, Lemma 2, Theorem 3 (Diff-Flow), Theorem 4 (Split-Flow), Theorem 1, <https://doi.org/10.1089/cmb.2021.0444>, PMCID PMC8892959.
