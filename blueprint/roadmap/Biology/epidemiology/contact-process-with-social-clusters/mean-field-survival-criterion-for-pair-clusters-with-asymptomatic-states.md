# Mean-field survival criterion for the clustered contact process with asymptomatic states

**Model.** Each site of $\mathbb{Z}^d$ carries a social cluster of $N$ individuals. The state of cluster $x$ is $\xi_t(x) = (i,j)$ with $i,j \in \mathbb{Z}_+$, $i + j \le N$, where $i$ counts infected asymptomatic and $j$ infected symptomatic individuals. With external infection rates $\lambda_1,\lambda_2 \ge 0$, internal infection rates $\phi_1,\phi_2 \ge 0$ and symptom-onset rate $\gamma \ge 0$, the transitions at cluster $x$ are

$$
\begin{aligned}
(0,0) &\to (1,0) &&\text{at rate } \textstyle\sum_{y \sim x} \sum_{i,j} (i\lambda_1 + j\lambda_2)\,\mathbf{1}\{\xi_t(y) = (i,j)\},\\
(i,j) &\to (i+1,j) &&\text{at rate } i\phi_1 + j\phi_2 \quad (i + j < N),\\
(i,j) &\to (i-1,j+1) &&\text{at rate } i\gamma,\\
(i,j) &\to (i-1,j) &&\text{at rate } i,\\
(i,j) &\to (i,j-1) &&\text{at rate } j.
\end{aligned}
$$

New infections are always asymptomatic, and every infected individual recovers at rate $1$. Replacing the lattice by a homogeneously mixing population gives the mean-field system of ODEs for the densities $u_{ij}$ of clusters in state $(i,j)$; the mean-field model is said to survive if this system has a fixed point with a positive density of infected clusters.

**Statement.** For clusters of size $N = 2$, the mean-field model survives if and only if

$$
(\lambda_1 + \gamma\lambda_2)\bigl((1+\phi_1)(1+\phi_2) + (1+\phi_1) + \gamma(1+\phi_2)\bigr) > \gamma\phi_1 + \phi_2 + (1+\gamma)(2+\gamma).
$$

In particular survival is monotone in each of the four infection rates $\lambda_1,\lambda_2,\phi_1,\phi_2$, but not in $\gamma$: there are infection rates for which the mean-field model dies out for small $\gamma$, survives for intermediate $\gamma$, and dies out again for large $\gamma$.

## Expansion

With $N = 2$ the cluster states are $(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)$, and the mean-field system is a set of ODEs for their six densities, with the healthy density driven by the external force of infection $\sum_{i,j}(i\lambda_1 + j\lambda_2)u_{ij}$. At an interior fixed point the within-cluster transitions (internal infection, symptom onset, recovery) are linear in the infected densities, so these can be solved in terms of the healthy density; substituting into the balance equation for the healthy state leaves one scalar condition, and a positive solution exists exactly when the displayed inequality holds. Monotonicity in the infection rates is read off the inequality; the non-monotonicity in $\gamma$ follows because $\gamma$ appears on both sides.

## Sources

- K. Belatreche, L. Belhadji and N. Lanchier, The contact process with social clusters and asymptomatic states, arXiv:2610.04323 (2026), Proposition 1 and Section 2 (mean-field model), <https://doi.org/10.48550/arXiv.2610.04323>.
