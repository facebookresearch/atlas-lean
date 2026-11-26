# Maximum parsimony structural variation with conflict resolution

**Setting.** Let $R = \{pe_1, \dots, pe_m\}$ be discordant paired-end reads, each with a finite set of candidate alignments, and let $\mathrm{MC} = \{V_1, \dots, V_n\}$ be candidate structural-variant (SV) clusters, each a set of alignments implying one SV (deletion, insertion, inversion, or a transposon insertion from a known mobile-element family). Cluster $V$ *covers* $pe$ if it contains one of the alignments of $pe$. Two clusters *conflict* in a haploid genome if one implied SV makes the other cluster's reads incoherent. The *conflict hypergraph* $\mathrm{CG}$ has vertex set $\mathrm{MC}$ and one hyperedge for each triple of pairwise conflicting clusters (diploid case); in the haploid case it is the ordinary conflict graph whose edges are conflicting pairs. A subset $\mathrm{SC} \subseteq \mathrm{MC}$ is *satisfiable* if it contains no (hyper)edge of $\mathrm{CG}$; in the haploid case these are exactly the independent sets of the conflict graph. Let $\delta(\mathrm{SC}, pe) = 1$ if no cluster of $\mathrm{SC}$ covers $pe$ and $0$ otherwise. For weights $k, l > 0$, the MPSV-CR problem asks for a satisfiable $\mathrm{SC}$ minimizing

$$g(\mathrm{SC}) = k\,|\mathrm{SC}| + l \sum_{pe \in R} \delta(\mathrm{SC}, pe).$$

**Proposition.**

1. (Diploid conflicts are triples) In a diploid genome two pairwise conflicting SVs can coexist on different haplotypes, but three pairwise conflicting SVs cannot.
2. (Reduction to set cover without conflicts) If $\mathrm{CG}$ has no hyperedges and $l > k$, every optimal $\mathrm{SC}$ covers every read that some cluster covers, and among such sets it minimizes $|\mathrm{SC}|$: the problem is then minimum set cover (the conflict-free MPSV problem), approximable within $O(\log m)$ by the greedy algorithm.
3. (Hardness) For every $k, l > 0$, MPSV-CR is NP-hard.
4. (Inapproximability, Theorem 4.1) For no constant $\varepsilon > 0$ can MPSV-CR on a haploid genome be approximated within a factor $n^{1 - \varepsilon}$ in polynomial time, unless $\mathrm{P} = \mathrm{NP}$.

## Expansion

(1) is the pigeonhole principle: two haplotypes can host at most two pairwise incompatible variants. (2): if some coverable read is uncovered, adding one cluster that covers it raises the cost by $k$ and lowers it by at least $l > k$, so an optimal solution leaves no coverable read uncovered; the remaining objective $k|\mathrm{SC}|$ is the set-cover objective. (3) follows by a reduction from minimum set cover, and (4) by a reduction that encodes independent sets of the conflict graph, so the conflict constraint alone already makes the problem as hard to approximate as maximum independent set. The practical heuristic is therefore a two-phase greedy algorithm whose read coverage is guaranteed by the [maximal satisfiable selection bound](read-coverage-guarantee-of-greedy-maximal-satisfiable-cluster-selection.md). The point of the conflict constraint is to replace ad hoc post-filtering of overlapping calls: under multiple mapping, the unconstrained parsimony solution reports mutually incompatible variants at repeat-rich loci.

## Sources

- F. Hormozdiari, I. Hajirasouliha, P. Dao, F. Hach, D. Yorukoglu, C. Alkan, E. E. Eichler, S. C. Sahinalp, "Next-generation VariationHunter: combinatorial algorithms for transposon insertion discovery", Bioinformatics 26 (2010) i350–i357, Section 4.1, Section 4.2, Section 4.2.1 and Theorem 4.1, <https://doi.org/10.1093/bioinformatics/btq216> (PMC2881400).
