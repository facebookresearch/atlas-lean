# Exchanged heat and hot subnetworks

Let $F$ be the [insulated heat diffusion matrix](insulated-heat-diffusion-matrix.md) of an interaction graph on genes $1, \dots, n$, and let $h \in \mathbb{R}_{\ge 0}^n$ be a vector of gene scores (for example mutation frequencies across tumours). The exchanged heat matrix is

$$E = F\, D_h, \qquad E_{ij} = F_{ij}\, h_j,$$

where $D_h = \operatorname{diag}(h)$; $E_{ij}$ is the heat that reaches gene $i$ when heat $h_j$ is placed on gene $j$, and is in general not symmetric. For a threshold $\delta > 0$, form the weighted directed graph $H_\delta$ on the genes with an edge $j \to i$ of weight $E_{ij}$ whenever $E_{ij} > \delta$. The hot subnetworks are the strongly connected components of $H_\delta$: maximal sets $C$ such that every $u \in C$ reaches every $v \in C$ by a directed path. The number and sizes of these subnetworks are tested against their distribution under permuted gene scores.

## Depends on

- [Insulated heat diffusion matrix](insulated-heat-diffusion-matrix.md)

## Expansion

Because $E_{ij} = F_{ij} h_j$ and $E_{ji} = F_{ji} h_i$ differ, a highly mutated gene (large $h_j$) sends heat to its neighbours without necessarily receiving heat from weakly mutated ones; strong connectivity therefore requires heat to flow in both directions along some cycle, which prevents a single very hot gene such as TP53 from absorbing every neighbour into one star-shaped component, as happened with the symmetric diffusion of the earlier HotNet. The threshold $\delta$ is chosen so that large components do not appear when the observed scores are placed on random graphs with the same degree sequence. Applied to 3,281 tumours from 12 cancer types, the method identified 14 significantly mutated subnetworks, including known cancer signaling pathways and less characterized complexes such as cohesin and condensin, many containing rarely mutated genes.

## Sources

- M. D. M. Leiserson, F. Vandin, H.-T. Wu, J. R. Dobson, J. V. Eldridge, et al., "Pan-cancer network analysis identifies combinations of rare somatic mutations across pathways and protein complexes", *Nature Genetics* 47 (2015), 106–114, Online Methods "Exchanged heat matrix", "Identification of hot subnetworks" and "Statistical test for subnetworks", <https://doi.org/10.1038/ng.3168> (PMC4444046).
