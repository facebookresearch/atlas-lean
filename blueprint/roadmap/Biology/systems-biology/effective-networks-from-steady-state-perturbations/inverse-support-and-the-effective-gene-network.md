# Inverse support and the effective gene network

**Lemma (inverse support).** Let $W \in \mathbb{R}^{n\times n}$ be nonsingular and regard it as the weighted adjacency matrix of a directed graph with an edge $j \to i$ iff $W_{ij} \ne 0$. If $(W^{-1})_{ij} \ne 0$, then the graph contains a directed path from $j$ to $i$ (of length $0$ when $i = j$).

**Setting.** A regulatory system $\dot z = f(z) + (u, 0)$ with observed species $x \in \mathbb{R}^N$, unobserved species $y \in \mathbb{R}^M$ and a constant perturbation $u \in \mathbb{R}^N$ acting only on observed species is linearized at a stable steady state. Up to noise, the steady-state shift $(x,y)$ caused by a small constant perturbation satisfies

$$\begin{pmatrix} u \\ 0 \end{pmatrix} = \begin{pmatrix} A & B\\ C & D\end{pmatrix}\begin{pmatrix} x\\ y\end{pmatrix}$$

(signs absorbed into the blocks), with $D$ nonsingular. Eliminating $y$ gives

$$u = \tilde A\,x, \qquad \tilde A = A - B D^{-1} C,$$

so perturbation data on observed species identify the Schur complement $\tilde A$, not $A$.

**Proposition (effective network).** If $\tilde A_{ij} \ne 0$, then in the full network either there is a direct regulation $j \to i$ between observed species, or there is a path from observed species $j$ to observed species $i$ whose interior vertices are all unobserved. The converse fails: contributions of several such paths can cancel, and $\tilde A$ determines neither $A,B,C,D$ nor the number $M$ of unobserved species.

## Expansion

Lemma: suppose there is no path from $j$ to $i \ne j$. Let $J$ be the set of vertices reachable from $j$ (so $j\in J$, $i\notin J$) and $I$ its complement. No edge leaves $J$ towards $I$, so after reordering $W = \begin{pmatrix} W_J & W_{J,I}\\ 0 & W_I\end{pmatrix}$ in block form with rows and columns indexed by $(J, I)$. Since $\det W = \det W_J \det W_I$, both diagonal blocks are invertible and

$$W^{-1} = \begin{pmatrix} W_J^{-1} & -W_J^{-1}W_{J,I}W_I^{-1}\\ 0 & W_I^{-1}\end{pmatrix},$$

whose $(I, J)$ block is zero; in particular $(W^{-1})_{ij} = 0$.

Proposition: $\tilde A_{ij} = A_{ij} - \sum_{k,l} B_{ik}(D^{-1})_{kl}C_{lj}$. A nonzero summand needs an edge from observed $j$ to unobserved $l$ ($C_{lj}\ne 0$), a path inside the unobserved subnetwork from $l$ to $k$ (by the lemma applied to $W = D$), and an edge from $k$ to observed $i$ ($B_{ik} \ne 0$). If no such path and no direct edge exist, every term vanishes. Sparse Bayesian network inference from perturbation experiments therefore recovers this effective network.

## Sources

- F. Steinke, M. Seeger, K. Tsuda, "Experimental design for efficient identification of gene regulatory networks using sparse Bayesian models", BMC Systems Biology 1 (2007) 51, section "Unobserved variables", Lemma 1, <https://doi.org/10.1186/1752-0509-1-51>, PMCID PMC2233642.
