# Alternating Eulerian tours and copy-number balance

**Interval-adjacency graph.** Partition a reference chromosome into intervals $I_j = [s_j, t_j]$, $j = 1,\dots,n$. The interval-adjacency graph $G = (V,E)$ has vertices $V = \{s_1,t_1,\dots,s_n,t_n\}$ and edges $E = E_I \cup E_R \cup E_A$: interval edges $e_I(j) = (s_j,t_j)$, reference edges $(t_j,s_{j+1})$ for $j < n$, and variant edges joining interval ends that are adjacent in the cancer genome but not in the reference. Telomeric vertices $T$ (for one chromosome, $T = \{s_1,t_n\}$) are incident only to interval edges. A cancer genome $I_{\alpha(1)} \cdots I_{\alpha(M)}$, $\alpha(i) \in \{\pm1,\dots,\pm n\}$, traverses $G$ alternating between interval edges and reference or variant edges. For a vertex $v$ write $e_I(v)$, $e_R(v)$ and $E_A(v)$ for its incident interval, reference and variant edges.

**Copy-number balance.** A multiplicity function $\mu : E \to \mathbb N$ is balanced if

$$\mu(e_I(v)) = \mu(e_R(v)) + \sum_{a \in E_A(v)} \mu(a)\qquad \text{for all } v \in V \setminus T. \tag{1}$$

**Theorem.**
1. (One chromosome.) For a connected interval-adjacency graph, a function $\mu$ satisfying (1) exists iff there is a multigraph $G_\mu$ with edge multiplicities $\mu$ containing an alternating Eulerian tour from $s_1$ to $t_n$. Imposing $\mu(e_I(j)) = c_j$ yields a cancer genome in which interval $j$ occurs exactly $c_j$ times.
2. (Several chromosomes, possibly lost telomeres.) For a multichromosomal interval-adjacency graph with telomeric vertex set $T$, $\mu$ satisfies (1) on $V \setminus T$ iff $G_\mu$ decomposes into edge-disjoint alternating tours, each beginning and ending in $T$, whose union is all of $E_\mu$.

**Maximum-likelihood multiplicities.** If concordant read pairs fall uniformly on the genome, the count $r_j$ in interval $j$ is Poisson with mean $\rho_j \mu_j$, where $\mu_j = \mu(e_I(j))$ and $\rho_j$ is the expected count per copy (proportional to the interval length $L_j$). The maximum-likelihood balanced multiplicities solve

$$\min_\mu\ \sum_{j=1}^n \big(\rho_j \mu_j - r_j \log(\rho_j \mu_j)\big)\quad \text{subject to (1)},$$

a separable convex objective under totally unimodular flow constraints on the associated bidirected graph, hence solvable in polynomial time as a network flow problem.

## Expansion

Condition (1) says that at every non-telomeric vertex the number of times the tour arrives by an interval edge equals the number of times it leaves by a reference or variant edge, which is the degree condition of Kotzig's theorem for alternating (properly two-coloured) Eulerian trails; connectivity then gives a single tour between the two telomeric vertices, while several telomeres give a family of tours, one per cancer chromosome. Solutions need not be unique: with perfect data the true genome is one solution, but tours that leave some variant edges at multiplicity $0$ are also consistent, which is what makes the formulation robust to false adjacencies.

## Sources

- L. Oesper, A. Ritz, S. J. Aerni, R. Drebin, B. J. Raphael, "Reconstructing cancer genomes from paired-end sequencing data", BMC Bioinformatics 13(Suppl 6):S10 (2012), Eq (1) and Theorem 1, Eqs (2)–(3), Theorem 2, <https://doi.org/10.1186/1471-2105-13-S6-S10>, PMCID PMC3358655.
