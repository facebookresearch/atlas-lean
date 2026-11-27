# Alternating Eulerian tours and copy-number balance

**Interval-adjacency graph.** Partition a reference chromosome into intervals $I_j = [s_j, t_j]$, $j = 1,\dots,n$. The interval-adjacency graph $G = (V,E)$ has vertices $V = \{s_1,t_1,\dots,s_n,t_n\}$ and edges $E = E_I \cup E_R \cup E_A$: interval edges $e_I(j) = (s_j,t_j)$, reference edges $(t_j,s_{j+1})$ for $j < n$, and variant edges joining interval ends that are adjacent in the cancer genome but not in the reference. Telomeric vertices $T$ (for one chromosome, $T = \{s_1,t_n\}$) are incident only to interval edges. A cancer genome $I_{\alpha(1)} \cdots I_{\alpha(M)}$, $\alpha(i) \in \{\pm1,\dots,\pm n\}$, traverses $G$ alternating between interval edges and reference or variant edges. For a vertex $v$ write $e_I(v)$, $e_R(v)$ and $E_A(v)$ for its incident interval, reference and variant edges.

**Copy-number balance.** Assume every variant edge joins two distinct interval ends. For a multiplicity function $\mu : E \to \mathbb N$, let $G_\mu$ be the multigraph on $V$ with $\mu(e)$ parallel copies of each edge $e$ (no copy when $\mu(e) = 0$). Then $\mu$ is balanced if

$$\mu(e_I(v)) = \mu(e_R(v)) + \sum_{a \in E_A(v)} \mu(a)\qquad \text{for all } v \in V \setminus T, \tag{1}$$

where $\mu(e_R(v)) = 0$ when $v$ has no reference edge. An alternating trail in $G_\mu$ alternates between interval edges and reference or variant edges; a telomeric trail is an alternating trail that begins and ends at vertices of $T$ with interval edges.

**Theorem.** Fix $\mu : E \to \mathbb N$.

1. (One chromosome.) $G_\mu$ has an alternating Eulerian trail from $s_1$ to $t_n$ (one telomeric trail using every edge copy of $G_\mu$ exactly once) if and only if $\mu$ satisfies (1), $\mu(e_I(1)) = \mu(e_I(n)) = 1$ when $n \ge 2$, and the edges with $\mu(e) > 0$ form a connected subgraph containing $s_1$ and $t_n$. For $n = 1$ the condition is $\mu(e_I(1)) = 1$. With $\mu(e_I(j)) = c_j$ such a trail spells a cancer genome in which interval $j$ occurs exactly $c_j$ times.
2. (Several chromosomes, possibly lost telomeres.) For a multichromosomal interval-adjacency graph with telomeric vertex set $T$, $\mu$ satisfies (1) if and only if the edge copies of $G_\mu$ partition into edge-disjoint alternating trails, each either a telomeric trail or a closed alternating trail through no vertex of $T$. If every connected component of the subgraph of edges with $\mu(e) > 0$ contains a vertex of $T$, the partition can be chosen to consist of telomeric trails only.

Balance alone does not give a single trail: for one interval ($n = 1$) with $\mu(e_I(1)) = 2$, condition (1) is vacuous, yet the two copies of the interval edge do not form one alternating trail from $s_1$ to $t_1$. A balanced cycle of positive multiplicity that avoids $T$ likewise cannot be covered by telomeric trails, even when the unweighted graph $G$ is connected. Oesper et al.'s Theorems 1–2 state the existential form, that some balanced $\mu$ exists if and only if some $G_\mu$ has the required tours; both sides hold for every connected $G$ (take the reference genome), so a tour is not asserted for every prescribed balanced assignment.

**Maximum-likelihood multiplicities.** If concordant read pairs fall uniformly on the genome, the count $r_j$ in interval $j$ is Poisson with mean $\rho_j \mu_j$, where $\mu_j = \mu(e_I(j))$ and $\rho_j$ is the expected count per copy (proportional to the interval length $L_j$). The maximum-likelihood balanced multiplicities solve

$$\min_\mu\ \sum_{j=1}^n \big(\rho_j \mu_j - r_j \log(\rho_j \mu_j)\big)\quad \text{subject to (1)},$$

a separable convex objective under the balance constraints, which the source writes as flow conservation on the associated bidirected graph.

## Depends on

- [Poisson law as a probability measure](../../../Probability/central-limit-theorems/poisson-limit-theorem/poisson-prob-measure.md)

## Proof depends on

- [Euler circuit criterion for directed multigraphs](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/hierholzer-s-algorithm-for-euler-circuits/exists-is-euler-circuit-iff.md)

## Expansion

Necessity: each pass of a trail through a non-telomeric vertex uses one interval edge and one reference or variant edge there, which is (1); a telomeric vertex meets only its interval edge, so a trail visits it only at an end, which forces multiplicity one at the two telomeres of a single trail. Sufficiency is Kotzig's theorem: a connected two-edge-coloured multigraph in which every vertex meets as many edges of one colour as of the other has a properly coloured (alternating) Eulerian circuit. Per connected component of the positive-multiplicity subgraph, the interval-edge copies at telomeric vertices are even in number (both colour-degree sums are even and agree off $T$); join them in pairs by new adjacency-coloured edges, apply Kotzig's theorem, and cut the circuit at the new edges. Components without a telomeric vertex give closed trails, which are circular chromosomes. Solutions need not be unique: with perfect data the true genome is one solution, but solutions that leave some variant edges at multiplicity $0$ are also consistent, which is what makes the formulation robust to false adjacencies.

## Sources

- L. Oesper, A. Ritz, S. J. Aerni, R. Drebin, B. J. Raphael, "Reconstructing cancer genomes from paired-end sequencing data", BMC Bioinformatics 13(Suppl 6):S10 (2012), Eq (1) and Theorem 1, Eqs (2)–(3), Theorem 2 (existential form); <https://doi.org/10.1186/1471-2105-13-S6-S10>, PMCID PMC3358655.
- A. Kotzig, "Moves without forbidden transitions in a graph", Matematický časopis 18 (1968), 76–80.
