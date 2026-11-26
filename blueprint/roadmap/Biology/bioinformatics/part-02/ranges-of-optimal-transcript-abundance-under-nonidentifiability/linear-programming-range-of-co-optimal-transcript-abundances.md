# Linear-programming range of co-optimal transcript abundances

**Model.** A splice graph is a DAG with source $S$, sink $T$, vertices for (partial) exons and edges for splice junctions; each transcript $T_j$ is an $S$–$T$ path with abundance $c_j\ge0$. In the standard generative model of RNA-seq quantification, a fragment $z$ is drawn by first choosing a transcript with probability $P(T_j)\propto c_j$ and then a fragment from it with known probability $P(z\mid T_j)$:

$$P(F\mid\{c_j\})=\prod_{z\in F}\ \sum_{j\in A_T(z)}P(T_j)\,P(z\mid T_j),$$

where $A_T(z)$ indexes the transcripts onto which $z$ maps.

**Proposition (indistinguishable abundances).** Let $\{J_i\}$ be the phasing paths (the junction sets spanned by single fragments; single junctions if every fragment spans one junction). Two abundance vectors $c,c'\ge0$ define the same fragment distribution whenever

$$\sum_{j:\,J_i\subseteq T_j}c_j=\sum_{j:\,J_i\subseteq T_j}c'_j\qquad\text{for every }J_i .$$

Hence, if $c$ is a maximum-likelihood estimate, every $c'\ge0$ satisfying these linear constraints is also optimal. The *range of optimal expression* of transcript $T_j$ is $[\min c'_j,\max c'_j]$ over this polytope, computed by two linear programs per transcript. Because the feasible set is convex, every value in the range is attained by some co-optimal estimate.

## Expansion

The likelihood depends on $c$ only through the total abundance on each phasing path, since these totals are the sufficient statistics of the fragment-generating model. Nonidentifiability is therefore a property of the linear map from transcript abundances to phasing-path totals: its fibre through the estimate is a polytope, and projecting that polytope onto coordinate $j$ gives an interval. A degenerate interval means the transcript's abundance is identifiable from the data, and a wide one bounds the error that no amount of sequencing depth can remove. A hybrid range $[\lambda l^1+(1-\lambda)l^0,\ \lambda u^1+(1-\lambda)u^0]$ interpolates between this reference-only range $[l^0,u^0]$ and the graph-quantification range $[l^1,u^1]$. A differential-expression call is flagged as questionable when the mean lower end in the up-regulated group falls below the mean upper end in the other group.

## Sources

- H. Zheng, C. Ma, C. Kingsford, "Deriving ranges of optimal estimated transcript expression due to nonidentifiability", *Journal of Computational Biology* 29(2):121–139 (2022), Sections 2.1, 2.2 and 2.5, <https://doi.org/10.1089/cmb.2021.0444>, PMCID PMC8892959.
