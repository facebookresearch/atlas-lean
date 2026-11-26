# Oriented incidence matrix of a multigraph

Let $V$ and $E$ be sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a multigraph; loops are allowed). Its oriented incidence matrix is the real $V \times E$ matrix

$$B_{v e} = [e^- = v] - [e^+ = v],$$

so that the column of an edge with distinct endpoints is $+1$ at $e^-$ and $-1$ at $e^+$, and the column of a loop is $0$. Distinct edges, including parallel ones, give distinct columns.

In a circuit, with $V$ the nodes and $E$ the branches (both finite) and each branch $e$ oriented from its tail $e^-$ to its head $e^+$, this is the electrical incidence matrix of the network: $+1$ at the tail and $-1$ at the head of each branch, the negation of the signed graph incidence, which has $+1$ at the head. With node potentials $\varphi$, the [branch voltages](../../../../Physics/electromagnetism-and-circuits/circuit-theory/tellegen-s-theorem-and-branch-power-balance/branch-voltage-eq-tail-sub-head.md) $B^\top \varphi$ are the tail potential minus the head potential.
