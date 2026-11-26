# Minimum-recombinant inheritance-vector recursion

**Setting.** A nuclear family has two genotyped parents and $c$ genotyped children, typed at ordered loci $l = 0,1,\dots,L$. An **inheritance vector** $\vec v \in \{0,1\}^{2c}$ records, for each of the $2c$ parent-to-child meioses, which of the parent's two homologous chromosomes was transmitted at a locus. At locus $l$, let $\mathcal V_l$ be the set of inheritance vectors that are consistent with the observed genotypes for some assignment of each parent's alleles to its two homologs. For two inheritance vectors, the Hamming distance $H(\vec w,\vec v)$ counts the meioses whose transmitted homolog switches, that is, the recombinations implied between consecutive loci.

**Recursion.** Define $R(0,\vec v) = 0$ for $\vec v \in \mathcal V_0$ and, for $l \ge 1$ and $\vec v \in \mathcal V_l$,

$$R(l,\vec v) = \min_{\vec w\in\mathcal V_{l-1}}\Big\{R(l-1,\vec w) + H(\vec w,\vec v)\Big\}.$$

**Proposition.** $R(l,\vec v)$ is the minimum, over all sequences $\vec v_0\in\mathcal V_0,\dots,\vec v_l\in\mathcal V_l$ with $\vec v_l = \vec v$, of the total number of implied recombinations $\sum_{t=1}^{l}H(\vec v_{t-1},\vec v_t)$. Hence $\min_{\vec v\in\mathcal V_L}R(L,\vec v)$ is the globally minimum number of recombinations for the whole chromosome, and backtracking the minimizing predecessors from an optimal final vector yields a minimum-recombinant haplotype assignment for all family members.

## Depends on

- [Inheritance Vector](../inheritance-vector.md): the inheritance vectors $\vec v \in \{0,1\}^{2c}$
- [Transition](../transition.md): the Hamming distance between inheritance vectors as the count of implied recombinations

## Proof depends on

- [Paths extracted after topological relaxation are shortest paths](../../../../ComputerScience/graph-algorithms/shortest-paths/shortest-paths-in-directed-acyclic-graphs/run-path-to-spec.md): the recursion is shortest-path relaxation on the layered (acyclic) graph, and backtracking yields an optimal path

## Expansion

The recursion is Bellman's shortest-path principle on a layered graph whose layer-$l$ nodes are the consistent inheritance vectors and whose edge costs are Hamming distances: an optimal path to $\vec v$ at locus $l$ extends an optimal path to some $\vec w$ at locus $l-1$. Because the parental allele-to-homolog assignment at a locus is determined by the inheritance vector, each node carries a unique phase, and backtracking recovers haplotypes. The minimization is global along the chromosome: a locus may admit a phase with fewer switches relative to its neighbour than the one chosen, yet not lie on any globally optimal path. A naive implementation keeps all $2^{2c}$ vectors per locus; most are uninformative or symmetric, and pruning them (keeping a single vector at the first locus and only the few vectors that informative loci distinguish) leaves the optimum unchanged while reducing time and memory by orders of magnitude. Replacing $H$ by negative log transition probabilities from a recombination model, as in the Lander–Green hidden Markov model, turns the same recursion into a Viterbi computation of maximum-likelihood haplotypes. Recombinations are counted only between typed loci, so double crossovers between adjacent markers are invisible.

## Sources

- A. L. Williams, D. E. Housman, M. C. Rinard and D. K. Gifford, "Rapid haplotype inference for nuclear families", Genome Biology 11 (2010), R108, Materials and methods, Eq. (1), <https://doi.org/10.1186/gb-2010-11-10-r108>, PMCID PMC3218664.
