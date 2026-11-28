# Sum-condition characterization of multi-state perfect phylogeny mixtures

**Setting.** There are $n$ characters (e.g. copy-number or SNV loci), each with $k$ states $\{0,\dots,k-1\}$, and $m$ bulk samples. A *frequency tensor* $\mathcal F=[f_{p,(c,i)}]$ records, for sample $p$ and character $c$, the fraction $f_{p,(c,i)}\ge0$ of cells in state $i$, with $\sum_if_{p,(c,i)}=1$. A *complete perfect phylogeny tree* $T$ is a rooted tree on $n(k-1)+1$ vertices whose edges are labelled by the character–state pairs $(c,i)$, $i\ge1$, each exactly once; the root has all characters in state $0$, and the vertices in state $i$ for character $c$ form a connected subtree. $T$ *generates* $\mathcal F$ if there is a usage matrix $U\ge0$ with rows summing to one (the clone proportions in each sample) such that $f_{p,(c,i)}=\sum_{(d,j)\in T_{(c,i)}}u_{p,(d,j)}$, i.e. $F=UB$ for the binary perfect-phylogeny matrix $B$ of $T$.

For a pair $(c,i)$ let $D_{(c,i)}$ be the set of states of character $c$ descending from $(c,i)$ in $T$, $f^+_p(D)=\sum_{l\in D}f_{p,(c,l)}$ the cumulative frequency, and $\delta(c,i)$ the children of $(c,i)$ in $T$.

**Theorem (multi-state sum condition).** $T$ generates $\mathcal F$ iff for all pairs $(c,i)$ and samples $p$,

$$f^+_p(D_{(c,i)})-\sum_{(d,j)\in\delta(c,i)}f^+_p(D_{(d,j)})\ge0,$$

and then the usage matrix is unique: $u_{p,(c,i)}$ equals the left-hand side.

**Theorem (ancestry-graph characterization).** Build the multi-state ancestry graph $G_{\mathcal F}$ with a vertex per pair and an edge $(c,i)\to(d,j)$ labelled $(D,D')$ for every valid descendant-set pair, i.e. $f^+_p(D)\ge f^+_p(D')$ in all samples (with $D'\subsetneq D$ when $c=d$). Then $T$ generates $\mathcal F$ iff $T$ is a *threaded* spanning tree of $G_{\mathcal F}$ (adjacent edges agree on the shared descendant set, and descendant sets of the same character are nested exactly along ancestry) satisfying the sum condition.

**Theorem (complexity).** Deciding whether a generating tree exists is NP-complete, even for $k=2$ states and $m=2$ samples; hence it is not fixed-parameter tractable in the number of samples. When the state trees of every character are given (cladistic case), solutions are the threaded spanning trees of a smaller cladistic ancestry graph, which can be enumerated.

## Expansion

In the two-state case $D_{(c,1)}=\{1\}$ and the condition reduces to the classical sum condition: a mutation's frequency must be at least the total frequency of its children. With more states, the cells "in state $i$ or a descendant state" are what a clone's subtree contributes, so cumulative frequencies replace raw frequencies. The uniqueness of $U$ follows because $B$ has full row rank $n(k-1)+1$.

## Sources

- Mohammed El-Kebir, Gryte Satas, Layla Oesper and Benjamin J. Raphael, "Multi-State Perfect Phylogeny Mixture Deconvolution and Applications to Cancer Sequencing", arXiv:1604.02605 (2016), Sections 2–4 (frequency tensor and complete perfect phylogeny tree definitions; the usage lemma; the MSSC characterization theorem; ancestry-graph theorem; NP-completeness for $k=m=2$; cladistic case), <https://doi.org/10.48550/arXiv.1604.02605>.
