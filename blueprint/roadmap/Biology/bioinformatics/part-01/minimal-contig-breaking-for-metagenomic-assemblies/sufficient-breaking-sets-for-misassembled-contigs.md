# Sufficient breaking sets for misassembled contigs

**Setting.** Let $G=(V,E)$ be a directed multigraph with $m$ sources and $m$ sinks in which every other vertex has equal in- and out-degree; it models a fully contracted de Bruijn graph of assembled contigs, with vertices the repeat-free segments and edges the junctions where a contig might be misassembled. A *feasible ground truth* is a set of $m$ edge-disjoint source-to-sink trails partitioning $E$; let $\mathcal G_T$ be the set of all of them (the assembled contig set $C$ is one). For a trail set $g$ and $R\subseteq E$, $g\setminus R$ denotes the trails cut at the edges of $R$. Trail sets $T_1,T_2$ are *consistent* if every trail of $T_1$ is contained in a trail of $T_2$ and vice versa. $R$ is a *sufficient breaking set* if $g_1\setminus R$ and $g_2\setminus R$ are consistent for all $g_1,g_2\in\mathcal G_T$; breaking the contigs at $R$ then leaves only junctions that every plausible genome agrees on.

**Proposition 1.** $R$ makes $C\setminus R$ consistent with $g\setminus R$ for every $g\in\mathcal G_T$ iff $R$ is a sufficient breaking set; so sufficiency does not depend on which ground truth produced the contigs.

**Algorithm (Eq. 2).** With a Boolean $b_e$ per edge, choose a minimum-cardinality set $R=\{e:b_e\}$ satisfying

$$\Phi(b)=\bigwedge_{v:\ |\mathrm{Pred}(v)|\ge2,\ |\mathrm{Succ}(v)|\ge2}\Big(\bigwedge_{e\in\mathrm{In}(v)}b_e\ \vee\ \bigwedge_{e\in\mathrm{Out}(v)}b_e\Big),$$

i.e. at every vertex with at least two distinct predecessors and two distinct successors, cut all incoming or all outgoing edges; the problem decomposes over connected components.

**Proposition 3.** If $G$ is fully contracted, a minimum-cardinality solution $R$ of Eq. 2 is a sufficient breaking set.

**Proposition 4.** If moreover $G$ is a DAG without parallel edges, the minimum-cardinality solution of Eq. 2 is a sufficient breaking set of optimal (minimum) cardinality.

## Expansion

At a vertex $v$ with two predecessors $x,x'$ and two successors $y,y'$, ground truths can route either $x\,v\,y$ and $x'\,v\,y'$ or the swapped pairs; unless every passage through $v$ is cut on one side, some unbroken piece $x\,v\,y$ appears in one ground truth but in no trail of the other. Cutting all of one side removes every such ambiguity, and in a fully contracted graph vertices with a single predecessor or successor force their junctions, so no other cut is needed (Proposition 3). For optimality in a DAG without parallel edges, the swap argument shows every sufficient breaking set must contain all in-edges or all out-edges of each such vertex, so Eq. 2's minimum is a lower bound (Proposition 4). On the running example with contigs $abcde$, $fbcg$, $hcdi$, breaking at the starts of all long repeats needs four cuts while the optimum, matching the min cut, is three. Minimality matters once parallel edges are present. In that example, with edges $ab, fb, bc_1, bc_2, hc, cd_1, cd_2, cg, de, di$, the set $R=\{bc_1,bc_2,hc,cd_1\}$ satisfies $\Phi$ (it is all of $\mathrm{In}(c)$ plus one of the two parallel edges from $c$ to $d$), yet for the ground truth $\{abcde,fbcdi,hcg\}$ one routing of the parallel edges leaves the piece $c\,d\,i$ and the swapped routing leaves only $c\,d\,e$, $c$ and $d\,i$, so $R$ is not sufficient.

## Sources

- Lam KK, Hall R, Clum A, Rao S, "BIGMAC : breaking inaccurate genomes and merging assembled contigs for long read metagenomic assembly", BMC Bioinformatics 2016 Oct 28;17:435, problem formulation, Equations (2)-(3) and Propositions 1-4, <https://doi.org/10.1186/s12859-016-1288-y>, PMCID PMC5084376.
