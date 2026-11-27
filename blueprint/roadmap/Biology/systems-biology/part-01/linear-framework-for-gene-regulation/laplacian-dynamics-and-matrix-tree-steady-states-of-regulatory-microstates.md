# Laplacian dynamics and matrix-tree steady states of regulatory microstates

**Setting.** Let $G$ be a finite directed graph with vertices $1, \dots, n$ (microstates of a regulatory region, with $1$ the reference microstate) and labelled edges $i \xrightarrow{a} j$, where the label $a > 0$ is the transition rate from $i$ to $j$ (labels may include concentrations of transcription factors, held fixed by timescale separation). The *Laplacian* $\mathcal L(G)$ is the $n \times n$ matrix with $\mathcal L_{ji} = a$ for each edge $i \xrightarrow{a} j$ ($i \ne j$, summing labels of parallel edges) and $\mathcal L_{ii} = -\sum_{j \ne i} \mathcal L_{ji}$. The microstate probabilities $u(t)$ obey the linear master equation

$$\frac{d u}{dt} = \mathcal L(G)\, u, \qquad \mathbf 1^{\mathsf T} \mathcal L(G) = 0,$$

so total probability is conserved.

**Steady states when $G$ is strongly connected.** Then $\ker \mathcal L(G)$ is one-dimensional, spanned by a vector $\rho^G$ with all entries positive, and the unique steady-state probabilities are

$$u_j^* = \frac{\rho^G_j}{\rho^G_1 + \cdots + \rho^G_n}.$$

1. *At thermodynamic equilibrium (detailed balance).* Every edge $i \xrightarrow{a} j$ has a reverse edge $j \xrightarrow{b} i$, and each such pair is separately balanced at steady state. Choosing any path of reversible edges $1 = i_1 \rightleftharpoons i_2 \rightleftharpoons \cdots \rightleftharpoons i_{p+1} = j$ with forward labels $a_k$ and reverse labels $b_k$,

    $$\rho^G_j = \prod_{k=1}^{p} \frac{a_k}{b_k},$$

    independent of the path by the cycle condition. Via $a/b = \exp(-\Delta G / RT)$ this recovers the Boltzmann weights of the equilibrium thermodynamic formalism, and the denominator is the partition function.

2. *Away from equilibrium (matrix-tree theorem).* For general strongly connected $G$, with $\Theta_j(G)$ the set of spanning trees of $G$ rooted at $j$ (every vertex has a directed path to $j$ in the tree, and $j$ has no outgoing tree edge),

    $$\rho^G_j = \sum_{T \in \Theta_j(G)} \ \prod_{(k \xrightarrow{a} l) \in T} a .$$

A graph is strongly connected iff it has a spanning tree rooted at every vertex, so every microstate has positive steady-state probability, and the denominator is a non-equilibrium partition function.

**Non-strongly connected graphs.** Each terminal strongly connected component $\mathcal T_1, \dots, \mathcal T_t$ (one with no edges leaving it) contributes a basis vector of $\ker \mathcal L(G)$, obtained by applying the tree formula within that component and setting all other entries to $0$; every steady state is a linear combination of these, and microstates outside terminal components have zero steady-state probability.

## Expansion

Detailed balance makes the flux across each reversible pair vanish separately, so $u^*_j = (a/b)\, u^*_i$ along each edge; multiplying along a path gives the product formula, and consistency around cycles is the Kolmogorov cycle condition. Away from equilibrium, the directed matrix-tree theorem identifies the cofactors of $\mathcal L(G)$ with rooted spanning-tree polynomials, and the vector of these cofactors lies in the kernel because the columns of $\mathcal L(G)$ sum to zero. Equilibrium imposes history independence (any path gives the same weight); non-equilibrium steady states depend on all spanning trees and thus on the entire graph, which is why irreversible steps (polymerase initiation, nucleosome remodelling, chromatin-mark turnover) can produce gene-regulation functions unattainable at equilibrium. Sequences and trees of reversible edges always satisfy detailed balance even if the edges are individually dissipative.

## Sources

- T. Ahsendorf, F. Wong, R. Eils, J. Gunawardena, "A framework for modelling gene regulation which accommodates non-equilibrium mechanisms", BMC Biology (2014), Results, "Laplacian dynamics" (Eqs. 1–4), "At thermodynamic equilibrium" (Eqs. 5–6), "Away from equilibrium" (Eq. 7, matrix-tree formula), "Non-strongly connected graphs" (terminal strongly connected components). <https://doi.org/10.1186/s12915-014-0102-4> (PMC4288563).
