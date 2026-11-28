# Giant component of multi-community random contact graphs

**Model.** A population is split into $r$ communities $V_1,\dots,V_r$ with $|V_i|=n_i$ and $n=\sum_in_i$. Each pair $v\in V_i$, $u\in V_j$ is joined independently with probability

$$p_{ij}=\frac{\lambda_{ij}}{\sqrt{n_in_j}},\qquad \lambda_{ij}=\lambda_{ji}\ge0,$$

an edge meaning that infection would pass between the two individuals; the final outbreak started from $v$ is the connected component of $v$. Let $M_{ij}=p_{ij}n_j=\lambda_{ij}\sqrt{n_j/n_i}$, the mean number of type-$j$ individuals infected by one type-$i$ individual, and let $\rho(M)$ be its spectral radius (Perron–Frobenius eigenvalue), the basic reproduction number.

**Theorem.** Fix $r$, $A$ and $\varepsilon>0$. Suppose $n$ is large, $n_i\le An_j$ for all $i,j$, the interaction pattern $\Lambda=(\lambda_{ij})$ is connected, and each $\lambda_{ij}$ is either $0$ or in $[\varepsilon,1/\varepsilon]$. Then, with probability $1-o(1)$:
1. if $\rho(M)\le1-\varepsilon$, every connected component has size $o(n)$ (no large outbreak);
2. if $\rho(M)\ge1+\varepsilon$, there are $\alpha_1,\dots,\alpha_r>0$ and a component $C$ with $\bigl||C\cap V_i|-\alpha_in_i\bigr|=o(n)$ for every $i$, while all other components have polylogarithmic size.

Here $\alpha_i$ is the survival probability of the multi-type Galton–Watson process started from one type-$i$ individual, in which a type-$i$ individual has $\mathrm{Bin}(n_j,p_{ij})$ children of type $j$; the extinction vector $1-\alpha$ is the minimal nontrivial fixed point of the offspring generating map $f$, with all coordinates below one.

## Expansion

Exploring the component of a vertex is, up to $o(n)$ explored vertices, a multi-type branching process with mean matrix $M$; it survives with positive probability exactly when $\rho(M)>1$. In the supercritical case, vertices whose local exploration survives join a single giant component (sprinkling arguments connect them), so the fraction of community $i$ ultimately infected is $\alpha_i$. Early in the epidemic, the type composition of new infections aligns with the Perron–Frobenius eigenvector of $M$. The model contains Erdős–Rényi ($r=1$) and bipartite random graphs as special cases.

## Sources

- Dor Minzer, Yaron Oz, Muli Safra and Lior Wainstain, "Pandemic Spread in Communities via Random Graphs", arXiv:2101.05354 (2021), Section 1 (model and Theorem 1.1) and Theorem 2.8 (numbering of v1 and v2), <https://doi.org/10.48550/arXiv.2101.05354>.
