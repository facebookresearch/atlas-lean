# Supermodular upper bound on infections under edge deletion in the discrete-time networked SIS model

**Model.** On an undirected graph with $N$ nodes, let $x_i(t)$ be the infection probability of node $i$, $B_{ij} \ge 0$ the mean infection rate across edge $(i,j)$, $D_i \ge 0$ the mean healing rate, and $h \in (0,1]$ the sampling step. The discrete-time mean-field SIS (D-SIS) model is

$$
\mathbf{x}(t+1) = (I - hD)\mathbf{x}(t) + h(I - X(t))B\mathbf{x}(t), \qquad X(t) = \mathrm{diag}(x_i(t)),
$$

under the assumptions $hD_i < 1$, $h\sum_{j \ne i} B_{ij} < 1$, and $B$ irreducible. Deleting a set $P$ of edges from a candidate set $Q$ gives the transition matrix $M_{-P} = I - hD + hB_{-P}$, with $\mathbf{x}(t+1) \le M_{-P}\mathbf{x}(t)$ componentwise. Two quantities measure the outbreak: the **increased number of infections** $\sigma(P) = \|\mathbf{x}^* - \mathbf{x}(0)\|_1$ with $x^*_i = \sup_t x_i(t)$, and the **cumulative infection variation** $\sigma'(P) = \sum_{l=0}^{t-1}\|\mathbf{x}(l) - \mathbf{x}(l+1)\|_1$. Choosing $k$ edges to minimize $\sigma$ is NP-hard.

**Theorem.** If $\rho(M_{-P}) < 1$, then

$$
\sigma(P) \le \sigma'(P) \le \hat\sigma(P) := \mathbf{1}^\top (M_{-P} + hD - I)(I - M_{-P})^{-1}\mathbf{x}(0).
$$

**Proposition.** $\hat\sigma(P)$ is non-increasing and supermodular in the deleted edge set $P \subseteq Q$. It is therefore used as a polynomial-time surrogate: a greedy algorithm deletes, one at a time, the candidate edge giving the largest decrease of $\hat\sigma$.

## Depends on

- [Spectral radius and die-out of SIS epidemics](../../epidemiology/epidemics-on-networks/spectral-radius-and-die-out-of-sis-epidemics.md)

## Expansion

Dropping the factor $(I - X(t)) \le I$ dominates the trajectory by the linear positive system driven by $M_{-P}$. Summing the geometric series $\sum_t M_{-P}^t = (I - M_{-P})^{-1}$, which converges when $\rho(M_{-P}) < 1$, bounds the total new infections; the factor $M_{-P} + hD - I = hB_{-P}$ isolates the infection inflow. Removing edges lowers $B_{-P}$ entrywise, so $\hat\sigma$ is non-increasing. Supermodularity (diminishing returns of successive deletions) is established as for the analogous bound for discrete-time SIR spreading, which this result extends to SIS dynamics.

## Sources

- Hoang Phi Dung, Duong Khanh Ly, "Minimizing cumulative infections in SIS epidemic models over networks via an edge deletion algorithm", arXiv (2026). Section 2 (D-SIS model, definitions of $\sigma$ and $\sigma'$), Section 3 (upper-bound theorem, supermodularity proposition, greedy edge deletion algorithm). <https://doi.org/10.48550/arXiv.2606.30142>
