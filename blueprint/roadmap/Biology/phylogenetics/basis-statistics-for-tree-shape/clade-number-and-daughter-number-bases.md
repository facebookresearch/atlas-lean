# Clade-number and daughter-number bases of tree statistics

Let $\mathcal{T}_n$ be the rooted binary tree shapes with $n\ge 2$ leaves. A **basis of statistics** is a vector $\mathcal{B}(T)=(B_1(T),\dots,B_r(T))^{t}$ of functions $B_i:\mathcal{T}_n\to\mathbb{R}$; a statistic $A$ is **represented** by $\mathcal{B}$ if $A(T)=\mathbf{a}^{t}\mathcal{B}(T)$ for a fixed coefficient vector $\mathbf{a}$ and all $T\in\mathcal{T}_n$.

- The **clade-number basis** is $\mathcal{C}=(C_2,\dots,C_n)$, where $C_r(T)$ is the number of inner vertices whose clade has exactly $r$ leaves.
- The **daughter-number basis** is $\mathcal{D}=(D_{i,j})$ for $1\le i\le\lfloor n/2\rfloor$, $i\le j\le n-i$, where $D_{i,j}(T)$ is the number of inner vertices whose two daughter clades have sizes $i$ and $j$.

Properties:

1. $C_r(T)=\sum_{i=1}^{\lfloor r/2\rfloor}D_{i,r-i}(T)$, so $\mathcal{D}$ refines $\mathcal{C}$: every statistic represented by $\mathcal{C}$ is represented by $\mathcal{D}$.
2. $C_n(T)=1$ and $C_2(T)+\dots+C_{n-1}(T)=n-2$, so the image of $\mathcal{T}_n$ under $\mathcal{C}$ has affine dimension at most $n-3$. The daughter numbers satisfy $n-1$ linear identities, so the image under $\mathcal{D}$ has dimension at most $\lfloor (n-2)/2\rfloor\,\lceil (n-2)/2\rceil$.
3. If $\boldsymbol{\mu}=\mathbb{E}[\mathcal{B}(T)]$ and $\boldsymbol{\Sigma}=\mathrm{Cov}[\mathcal{B}(T)]$ under any distribution on $\mathcal{T}_n$, then represented statistics $A_k=\mathbf{a}_k^{t}\mathcal{B}$ satisfy $\mathbb{E}[A_1]=\mathbf{a}_1^{t}\boldsymbol{\mu}$ and $\mathrm{Cov}[A_1,A_2]=\mathbf{a}_1^{t}\boldsymbol{\Sigma}\,\mathbf{a}_2$.

Examples: the Sackin index is $S(T)=\sum_{r=2}^n r\,C_r(T)$, the $\hat{s}$-shape statistic is $\sum_{r=2}^n\log(r-1)\,C_r(T)$, and the Colless index $\sum_{i,j}(j-i)D_{i,j}(T)$ is represented by $\mathcal{D}$ but not by $\mathcal{C}$. Among the balance indices surveyed, 17 are represented by at least one of the two bases, while indices such as the variance of leaf depths, the $B_1$ and $B_2$ indices and the maximum depth are represented by neither. A statistic is shown not to be represented by $\mathcal{B}$ by exhibiting $T_1,T_2$ with $\mathcal{B}(T_1)=\mathcal{B}(T_2)$ but $A(T_1)\ne A(T_2)$, or, when $A$ is a nonlinear function of $\mathcal{B}$, by showing that the linear system for $\mathbf{a}$ over all trees is inconsistent.

## Expansion

Each inner vertex contributes to exactly one clade number and one daughter number, which gives the refinement identity. The root is the unique clade of size $n$, and a binary tree has $n-2$ non-root inner vertices. A second way of counting clades of size $r$ (as daughters of size $r$ of some vertex) gives the extra identities among daughter numbers. Property 3 is linearity of expectation and bilinearity of covariance.

## Sources

- Daniel J. Bauman, Noah A. Rosenberg, "Basis statistics for phylogenetic tree shape: tree balance formulas beyond expectations", arXiv:2610.40894 (2026), Sections 3 and 4 (Table 1), Appendices A to C, <https://doi.org/10.48550/arXiv.2610.40894>
