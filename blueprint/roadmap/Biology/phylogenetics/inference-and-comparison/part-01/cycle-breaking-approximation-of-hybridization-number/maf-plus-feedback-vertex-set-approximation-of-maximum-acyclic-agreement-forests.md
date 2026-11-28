# MAF plus feedback vertex set approximation of maximum acyclic agreement forests

**Definitions.** Let $T_1, T_2$ be rooted binary phylogenetic trees on the same taxon set. A forest $\mathcal F$ (a set of trees) is a forest for $T$ if, for every component $F$, $T|_{L(F)}$ is isomorphic to $F$ and the subtrees $T(L(F))$ are vertex-disjoint with leaf sets partitioning $L(T)$; it is an *agreement forest* of $T_1, T_2$ if it is a forest for both. Its inheritance graph has the components as vertices and an arc $(F, F')$ whenever, in $T_1$ or in $T_2$, there is a directed path from the root of $T_i(L(F))$ to the root of $T_i(L(F'))$; the forest is *acyclic* if this graph is acyclic. Write $\mathrm{MAF}(T_1,T_2)$ and $\mathrm{MAAF}(T_1,T_2)$ for the minimum of $|\mathcal F| - 1$ over agreement forests and over acyclic agreement forests. The reticulation number of a rooted network $N$ with root $\rho$ is $r(N) = \sum_{v \ne \rho} (\delta^-(v) - 1)$, and $\mathrm{MAAF}(T_1,T_2)$ equals the minimum of $r(N)$ over networks displaying both trees (the hybridization number); an acyclic agreement forest with $k+1$ components converts to a displaying network with reticulation number $k$ and conversely.

**Extended inheritance graph.** Given an agreement forest $M$, let $D$ have one vertex for each vertex of $M$ with outdegree $2$, and an arc $u \to v$ whenever $T_1$ or $T_2$ contains a directed path from $u$ to $v$.

**Lemma (cycle breaking).** A set $V'$ of vertices of $D$ is a feedback vertex set of $D$ if and only if removing $V'$ from $M$ (deleting the edges above them and cleaning up) yields an acyclic agreement forest.

**Lemma (splitting bound).** For every agreement forest $M$ there is an acyclic agreement forest obtained from $M$ by removing edges whose size is at most $\mathrm{MAAF}(T_1,T_2) + |M|$.

**Theorem.** If Maximum Agreement Forest admits a $c$-approximation and Directed Feedback Vertex Set admits a $d$-approximation, then Maximum Acyclic Agreement Forest, and hence the hybridization number of two rooted binary trees, admits a $d(c+1)$-approximation: compute an agreement forest $M$ with the MAF algorithm, build $D$, compute a feedback vertex set $V$ of $D$ with the DFVS algorithm, and remove $V$ from $M$. With exact MAF and exact DFVS solvers ($c = d = 1$) the output is within a factor $2$ of the hybridization number.

## Depends on

- [Rooted maximum agreement forest number](../../../../not-yet-classified/rooted-spragreement-forest/rooted-maf-number.md)

## Expansion

From the MAF guarantee, $|M| - 1 \le c\,\mathrm{MAF} \le c\,\mathrm{MAAF}$. The splitting bound comes from cutting $T_1$ along the union of the edge sets that produce $M$ and an optimal acyclic forest; the result agrees with both trees, is acyclic because it refines an acyclic forest, and refines $M$. Combining the two, an optimal splitting of $M$ has size at most $(c+1)\,\mathrm{MAAF} + 1$. Every directed cycle in the inheritance graph of a refinement of $M$ lifts to a cycle among outdegree-2 vertices of $M$ and conversely, which is the cycle-breaking lemma; removing a minimum feedback vertex set adds exactly one component per removed vertex, so the optimal splitting has size $|M| + |\mathrm{MFVS}|$. Removing a $d$-approximate set $V$ gives $|\mathcal F| - 1 = |M| + |V| - 1 \le d(|M| + |\mathrm{MFVS}| - 1) \le d(c+1)\,\mathrm{MAAF}$. Both subproblems are NP-hard but have fast fixed-parameter solvers, so the exact-subroutine mode is exponential in the worst case yet handled trees far larger than exact hybridization-number solvers, with observed ratios averaging about $1.003$ on simulated binary instances. For nonbinary trees the analogous construction gives a $d(c+3)$-approximation.

## Sources

- L. van Iersel, S. Kelk, N. Lekić, C. Scornavacca, "A practical approximation algorithm for solving massive instances of hybridization number for binary and nonbinary trees", BMC Bioinformatics 15:127 (2014), Theorem 1, Lemmas 2-3 and Equations 1-2 (section "The algorithm for binary trees"), <https://doi.org/10.1186/1471-2105-15-127>, PMCID PMC4023542.
