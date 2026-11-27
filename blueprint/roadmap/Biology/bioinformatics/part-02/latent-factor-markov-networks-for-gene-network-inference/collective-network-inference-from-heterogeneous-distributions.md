# Collective network inference from heterogeneous data distributions

Use the latent-factor parameterization of [Latent-factor Poisson neighbourhood regression](latent-factor-poisson-markov-network.md): gene $s$ has a factor $u_s \in \mathbb{R}^r$, edge weights are products of factors through a component-interaction matrix $W$, and the network is the union of estimated neighbourhoods.

**Latent-factor multinomial model.** Let each $X_s$ take values in $\{1, \dots, m\}$, with value $m$ as reference. The node-conditional law is a multiclass logistic (softmax) regression on the indicators $I_k(X_t) = \mathbf{1}[X_t = k]$:

$$P(X_s = j \mid X_{V\setminus s}) = \frac{\exp\big(\theta_{sj} + \sum_{t \ne s}\sum_{k} \theta_{st;jk} I_k(X_t)\big)}{1 + \sum_{l} \exp\big(\theta_{sl} + \sum_{t \ne s}\sum_k \theta_{st;lk} I_k(X_t)\big)}, \qquad j = 1, \dots, m-1,$$

with node-wise terms collected in $Q \in \mathbb{R}^{p \times (m-1)}$ and pairwise terms factorized as

$$\theta_{st;jk} = u_s^{\top} Q_{sj} W^{\top} W Q_{tk} u_t .$$

The neighbourhood is $\hat N(s) = \{t \ne s : \sum_{j,k} u_s^{\top} Q_{sj} W^{\top} W Q_{tk} u_t \ne 0\}$, and $U, Q, W$ minimize the summed node-wise multinomial negative log-likelihoods plus elastic-net penalties on $U$, $Q$ and $W$.

**Collective inference (data fusion).** Let $D_x$ ($n_x$ samples) and $D_y$ ($n_y$ samples) be measurements of the same $p$ genes, each modelled by a family of node-conditional exponential-family regressions $P_x$, $P_y$ that may differ in parameters or in type (for example Poisson and multinomial), with nodewise losses $\ell_{s;P}$ as in the single-dataset case. The fused estimator solves

$$\min_{U, Q_x, Q_y, W_x, W_y}\ \sum_{s \in V}\Big(\ell_{s; P_x}(U, Q_x, W_x; D_x) + \ell_{s; P_y}(U, Q_y, W_y; D_y)\Big) + \text{penalty},$$

with the latent factors $U$ **shared** across datasets and the interaction matrices $W_x, W_y$ and distribution parameters $Q_x, Q_y$ **specific** to each (for a Poisson dataset $Q_x = I$; the penalty is $\lambda(\mathrm{Reg}(U) + \mathrm{Reg}(W_x) + \mathrm{Reg}(Q_y) + \mathrm{Reg}(W_y))$ in the Poisson–multinomial case). The estimated neighbourhood of $s$ collects genes linked to it under either distribution,

$$\hat N(s) = \{t \ne s : \hat\theta_{st; P_x} \ne 0 \ \text{or}\ \hat\theta_{st; P_y} \ne 0\},$$

with $\hat\theta_{st;P_x} = u_s^{\top} W_x^{\top} W_x u_t$ and $\hat\theta_{st;P_y} = \sum_{j,k} u_s^{\top} Q_{y,sj} W_y^{\top} W_y Q_{y,tk} u_t$. The formulation extends to any number of datasets and to any exponential family whose pairwise weights are written as such factor products. The estimator is a nodewise fitting procedure: a family of fitted conditionals is the set of conditionals of a joint Markov network only when that network is normalizable, which for the Poisson component requires all $\hat\theta_{st;P_x} \le 0$, so $\hat N(s)$ is in general a union of regression neighbourhoods. The multinomial conditionals, by contrast, always come from a joint pairwise discrete Markov network, since the state space is finite.

## Depends on

- [Latent-factor Poisson neighbourhood regression](latent-factor-poisson-markov-network.md)

## Expansion

The coupling is through $u_s$: it appears in the loss terms of every dataset, so a good factor must fit all of them at once, while each dataset keeps its own $W$ to model how its latent components interact and its own $Q$ for distribution-specific effects such as category biases. This lets datasets that disagree, or capture biology with different accuracy, inform a single graph without forcing them into one likelihood. In the multinomial model the edge $(s, t)$ is present when the pairwise term is nonzero for at least one pair of categories $(j, k)$, matching the Markov property of the softmax conditional, in which $X_t$ is irrelevant to $X_s$ exactly when all $\theta_{st;jk}$ vanish; the pairwise weights must also be symmetric, $\theta_{st;jk} = \theta_{ts;kj}$, which the factorization gives.

## Sources

- M. Žitnik and B. Zupan, "Gene network inference by fusing data from diverse distributions", Bioinformatics 31(12) (2015), i230–i239, Section 3.5 (Eqs. (10)–(12)), Section 3.6 and Section 3.7 (Eq. (13)), <https://doi.org/10.1093/bioinformatics/btv258> (PMC4542780).
