# Kermack–McKendrick modules and the next-generation conditions for Petri nets

A Petri net has compartments $x_1, \dots, x_k$ and transitions $z_1, \dots, z_l$ with rates $r_j > 0$. Let $m_{ij}$ be the number of arrows $x_i \to z_j$ and $n_{ij}$ the number of arrows $z_j \to x_i$. Its rate (mass-action) equation is

$$
x_i'(t) = \sum_{j=1}^{l} r_j (n_{ij} - m_{ij})\, x_1^{m_{1j}} \cdots x_k^{m_{kj}} .
$$

Fix disease compartments $S_I = \{x_1, \dots, x_s\}$. Fix three disjoint sets of transitions: susceptible transitions $T_S$ (demography), infection-process transitions $T_{IP}$ (new infections), and infection-module transitions $T_I$, meaning all other transitions with an input from $S_I$. Together these are the **Kermack–McKendrick (KM) modules**. The geometric conditions are:

- **(G1)** No arrows join $S_I$ and $T_S$, and no arrow goes from a compartment outside $S_I$ to a transition in $T_I$.
- **(G2)** If $z_j \in T_{IP}$ has no input from $S_I$, then it has no output to $S_I$.
- **(G3)** $n_{ij} \ge m_{ij}$ for $x_i \in S_I$ and $z_j \in T_{IP}$.
- **(G4)** $\sum_{i=1}^{s}(m_{ij} - n_{ij}) \ge 0$ for every $z_j \in T_I$.
- **(G5)** The rate equations of the net with the infection module removed have a locally asymptotically stable disease-free equilibrium.

**Lemma 1 and Theorem 2.** Under (G1), each disease compartment satisfies $x_i' = \mathcal{F}_i - \mathcal{V}_i$ with

$$
\mathcal{F}_i = \sum_{z_j \in T_{IP}} r_j (n_{ij} - m_{ij})\, x_1^{m_{1j}} \cdots x_k^{m_{kj}},
\qquad
\mathcal{V}_i = \sum_{z_j \in T_I} r_j (m_{ij} - n_{ij})\, x_1^{m_{1j}} \cdots x_s^{m_{sj}} .
$$

Under (G1)–(G4), this splitting satisfies the van den Driessche–Watmough hypotheses (A1)–(A4).

**Proposition 4 and Theorem 6.** Let $F = (\partial \mathcal{F}_i / \partial x_j)$ and $V = (\partial \mathcal{V}_i / \partial x_j)$ at the disease-free equilibrium. Then $F \ge 0$ entrywise and $V$ is a (possibly singular) M-matrix. If moreover $V$ is nonsingular and (G5) holds, the disease-free equilibrium is locally asymptotically stable when $R_0 = \rho(FV^{-1}) < 1$ and unstable when $R_0 > 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

(G1) removes demographic transitions from the disease equations, which gives the split. Hypothesis (A1) holds because $\mathcal{F}_i(0, y)$ only collects transitions in $T_{IP}$ with no disease input, and (G2) kills these. (A2), $\mathcal{F} \ge 0$, follows from (G3). For (A3), at $x_i = 0$ only terms with $m_{ij} = 0$ survive in $\mathcal{V}_i$, and they carry the sign of $-n_{ij} \le 0$. (A4), $\sum_i \mathcal{V}_i \ge 0$, is (G4). Differentiating, (G3) gives $F \ge 0$. The off-diagonal entries of $V$ are nonpositive without further hypotheses: by (G1) every $z_j \in T_I$ has all its inputs in $S_I$, so at the disease-free equilibrium $\partial \mathcal V_i/\partial x_k$ ($k \ne i$) collects only transitions whose single input arrow comes from $x_k$; for these $m_{ij} = 0$, and the entry is $-\sum_j r_j n_{ij} \le 0$. (Requiring (G3) on $T_I$ as well would, with (G4), force $m_{ij} = n_{ij}$ on $S_I \times T_I$ and so $\mathcal V \equiv 0$.) Since $\sum_i \mathcal{V}_i \ge 0$ vanishes at the equilibrium, the column sums of $V$ are nonnegative, so $V$ is an M-matrix. The Jacobian is block triangular, $\begin{pmatrix} F - V & 0 \\ J_{21} & J_{22} \end{pmatrix}$, with $J_{22}$ Hurwitz by (G5). The $R_0$ threshold for $F - V$ then gives the result. The $(i,k)$ entry of $FV^{-1}$ can also be read as a sum over paths in the net from $x_k$ to $x_i$ that cross exactly one infection-process transition. Each path is weighted by the flow of susceptibles at that transition times the product of branching ratios along the path.

## Sources

- Segovia C. Petri nets in epidemiology. *Journal of Mathematical Biology* 91 (2025) 40. <https://doi.org/10.1007/s00285-025-02272-3>. PMCID: PMC12441085.
