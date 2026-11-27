# Geometry-induced auxin peaks under weak active transport

**Setting.** Plant cells $i=1,\dots,n$ of a static tissue form the vertices of an undirected graph with neighbour sets $\mathcal N_i$. Each cell carries a vector $y_i\in\mathbb R_+^m$ of concentrations (auxin, PIN proteins, ...). A *concentration-based transport model* is

$$
\dot y_i=\pi(y_i)-\delta(y_i)+D\sum_{j\in\mathcal N_i}(y_j-y_i)+T\sum_{j\in\mathcal N_i}\big(\nu_{ji}-\nu_{ij}\big),
$$

with production $\pi$, decay $\delta$, diagonal passive diffusion $D$, and active (PIN-mediated) transport of strength $T\ge0$ whose flux from $i$ to $j$ factorizes as

$$
\nu_{ij}=\psi(y_i,y_j)\odot\varphi(y_j)\oslash\sum_{k\in\mathcal N_i}\varphi(y_k),
$$

i.e. cell $i$ allocates its transporters among neighbours in proportion to $\varphi(y_j)$. The Smith and Chitwood models of phyllotaxis are of this form.

**Lemma.** Let $\pi(y^*)=\delta(y^*)$, $\psi(y^*,y^*)\ne0$, $\varphi(y^*)\ne0$, and $D=0$.

1. If $T=0$, or if all cells have the same number of neighbours, the homogeneous state $y_i\equiv y^*$ is a steady state. On a finite tissue with $T\ne0$ it generically is not, because boundary cells have fewer neighbours.
2. If $0<T\ll1$, cells have different numbers of neighbours, and $\pi'(y^*)-\delta'(y^*)$ is nonsingular, there is a steady state

$$
y_i=y^*+T\,\xi_i\,\big[\pi'(y^*)-\delta'(y^*)\big]^{-1}\psi(y^*,y^*)+O(T^2),\qquad \xi_i=1-\sum_{j\in\mathcal N_i}\frac1{|\mathcal N_j|} .
$$

With passive transport ($D\ne0$), if moreover $J(y^*)+L\otimes D$ is nonsingular (for instance if $\pi'(y^*)-\delta'(y^*)$ is negative definite), then $y_i=y^*+T\eta_i+O(T^2)$ where $\big[J(y^*)+L\otimes D\big]\eta=(\xi_i\psi(y^*,y^*))_i$, $J$ block-diagonal with blocks $\pi'(y^*)-\delta'(y^*)$ and $L$ the (Neumann) graph Laplacian with $L_{ij}=1$ for $j\in\mathcal N_i$ and $L_{ii}=-|\mathcal N_i|$. The source's Remark 5.4 asks only that $\pi'(y^*)-\delta'(y^*)$ be nonsingular; that does not suffice: for $m=1$, a path of three cells and $\pi'-\delta'=3D$, the matrix $J+L\otimes D$ has kernel $(1,-2,1)$, the right-hand side is a nonzero multiple of it and so lies outside the range of this symmetric matrix, and no $\eta$ exists.

## Expansion

At the homogeneous state each cell sends $\psi^*/|\mathcal N_i|$ to every neighbour and receives $\psi^*/|\mathcal N_j|$ from neighbour $j$, so its net active influx is $-\xi_i\psi^*T$; this vanishes exactly in the interior set $\{\xi_i=0\}$ of a regular array and is nonzero at (and near) the boundary, where the neighbour count changes. Linearizing the kinetics then converts this imbalance into small peaks or dips proportional to $T\xi_i$. Hence, on bounded tissues, auxin peaks do not arise from a Turing instability in $T$ but as a smooth continuation of the homogeneous state, with amplitude and location encoded by tissue geometry: peaks first appear where cells have fewer neighbours. As $T$ grows, numerical continuation of the Smith and Chitwood models shows peaks added one by one from the boundary inwards through saddle-node bifurcations in a snaking diagram, so tissues can select among many stable multi-peak patterns depending on initial conditions; the picture persists on irregular tissues.

## Proof depends on

- [Implicit function theorem](../../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md)

## Sources

- Delphine Draelants, Daniele Avitabile, Wim Vanroose, "Localised auxin peaks in concentration-based transport models of the shoot apical meristem", arXiv:1403.3926 (2014), Section 2 (Hypotheses 1–2, Results 1–6), Section 5 (Definitions 5.1–5.2, Lemma 5.1, Remarks 5.2–5.4), <https://doi.org/10.48550/arXiv.1403.3926>.
