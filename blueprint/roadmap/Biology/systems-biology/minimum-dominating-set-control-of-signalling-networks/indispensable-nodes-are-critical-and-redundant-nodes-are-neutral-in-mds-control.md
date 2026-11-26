# Indispensable nodes are critical and redundant nodes are neutral in MDS control

Let $G = (V, E)$ be a finite undirected graph, or a directed graph with domination along edge directions, and let $N_D(G)$ be the size of a [minimum dominating set](one-step-controllability-from-a-minimum-dominating-set.md) (MDS). Classify a node $v$

- by its membership in MDSs: **critical** if $v$ lies in every MDS, **redundant** if it lies in no MDS, **intermittent** otherwise;
- by the effect of deleting it (with its incident edges), giving $G - v$: **indispensable** if $N_D(G - v) > N_D(G)$, **dispensable** if $N_D(G - v) < N_D(G)$, **neutral** if $N_D(G - v) = N_D(G)$.

**Proposition (Methods, Propositions 1 and 2 of the source).**

1. Every indispensable node is critical.
2. Every redundant node is neutral.

The converses fail: a node can be critical but neutral.

## Expansion

(1) If $v$ is not critical, some MDS $U$ avoids $v$; every node of $G - v$ outside $U$ was dominated by a node of $U$, which is not $v$, so $U$ still dominates $G - v$ and $N_D(G - v) \le N_D(G)$. (2) If $v$ is redundant, the same argument with any MDS shows $v$ is not indispensable. If $v$ were dispensable, an MDS $U$ of $G - v$ with $|U| = N_D(G) - 1$ would give the dominating set $U \cup \{v\}$ of $G$ of size $N_D(G)$, an MDS containing $v$, contradicting redundancy. These relations distinguish the MDS model from maximum-matching controllability, where the corresponding classes do not nest this way; in the human signalling network studied in the source all indispensable nodes were indeed MDS-critical and all redundant nodes neutral.

## Depends on

- [One-step controllability of a nonlinear network from a minimum dominating set](one-step-controllability-from-a-minimum-dominating-set.md)

## Sources

- V. Ravindran, J. C. Nacher, T. Akutsu, M. Ishitsuka, A. Osadcenco, V. Sunitha, G. Bagler, J.-M. Schwartz and D. L. Robertson, *Network controllability analysis of intracellular signalling reveals viruses are actively controlling molecular systems*, Scientific Reports 9 (2019), 2066. DOI: <https://doi.org/10.1038/s41598-018-38224-9>. PMCID: PMC6375943.
