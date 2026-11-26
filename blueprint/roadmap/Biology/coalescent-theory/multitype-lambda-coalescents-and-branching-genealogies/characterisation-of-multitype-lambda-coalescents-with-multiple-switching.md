# Characterisation of multitype Λ-coalescents with multiple switching

**Setting.** A $d$-type partition of $\mathbb{N}$ is a partition whose blocks each carry a type in $[d]$. A *multitype $\Lambda$-coalescent with multiple switching* is a Markov process $\bm\Pi$ on $d$-type partitions that is consistent (its restrictions to $[n]$ are Markov and compatible), partially exchangeable (law invariant under finite permutations preserving the initial type classes), and in which no other event happens at the same time as a merger; simultaneous type switches of several blocks are allowed.

**Coalescence mechanism.** For $J$ a set of current blocks and $i \in [d]$, let $\mathrm{coal}^i_J$ merge the blocks in $J$ into one block of type $i$. The multitype $\Lambda$-coalescent generator is
$$\mathcal{L}_{\mathrm{coal}}f(\bm\pi) = \sum_{i=1}^d\sum_{J}\big(f(\mathrm{coal}^i_J\bm\pi) - f(\bm\pi)\big)\lambda_{\bm\pi,J,i},$$
$$\lambda_{\bm\pi,J,i} = \sum_{k \ne i}\rho_{ik}\mathbf{1}\{|J| = 1, \text{type } k\} + \rho_{ii}\mathbf{1}\{|J| = 2, \text{both of type } i\} + \int_{[0,1]^d}\prod_{k=1}^d u_k^{|J_k|}(1-u_k)^{|J^c_k|}\,Q_i(du),$$
where $J_k$ ($J^c_k$) are the type-$k$ blocks in (outside) $J$, $\rho_{ik} \ge 0$, and $Q_i$ is a measure on $[0,1]^d$ without atom at $0$ with $\int \sum_k u_k^{1+\delta_{ik}}\,Q_i(du) < \infty$.

**Switching mechanism.** With rates $(a_{ik})_{i \ne k}$ and a measure $\nu$ on stochastic matrices satisfying $\int\sum_i(1 - u_{ii})\,\nu(dU) < \infty$, the dice generator changes the type vector $\mathfrak{t}$ of the blocks to $\tilde{\mathfrak{t}}$ at rate
$$\gamma_{\bm\pi,\tilde{\mathfrak{t}}} = \sum_i\sum_{k\ne i}a_{ik}\,\mathcal{I}_{i,k}(\mathfrak{t},\tilde{\mathfrak{t}}) + \int\prod_{i,k}u_{ik}^{|\{j : \mathfrak{t}_j = i,\ \tilde{\mathfrak{t}}_j = k\}|}\,\nu(dU),$$
where $\mathcal{I}_{i,k} = 1$ iff exactly one block changes, from type $i$ to type $k$.

**Theorem.** A process $\bm\Pi$ on $d$-type partitions is a multitype $\Lambda$-coalescent with multiple switching if and only if its generator decomposes as
$$\mathcal{L} = \mathcal{L}_{\mathrm{coal}} + \mathcal{L}_{\mathrm{dice}}$$
for some multitype $\Lambda$-coalescent mechanism $(\rho, Q)$ and an independent dice-process type-transition mechanism $(a, \nu)$. For $d = 1$ and no switching this reduces to Pitman's characterisation of $\Lambda$-coalescents, $\lambda_{b,k} = \Lambda(\{0\})\mathbf{1}_{k=2} + \int_{(0,1]}u^k(1-u)^{b-k}u^{-2}\Lambda(du)$.

## Expansion

Since mergers and switches never occur together, the generator splits into merger and pure-switch parts. Restricted to switches, the type vector of the blocks is a consistent, partially exchangeable Markov chain, hence a dice process: single-block switches at rates $a_{ik}$ plus coordinated switches in which every type-$i$ block independently rolls row $i$ of a random stochastic matrix. Restricted to mergers, consistency and partial exchangeability give the multitype paintbox representation of Johnston, Kyprianou and Rogers. Examples include the seed-bank coalescent with simultaneous switching, where coordinated dormancy initiation is a non-trivial $\nu$.

## Depends on

- [Dice processes characterise partially exchangeable consistent Markov chains](dice-processes-characterise-partially-exchangeable-consistent-markov-chains.md)

## Sources

- Adrián González Casanova, Noemi Kurt, Imanol Nuñez Morales and José Luis Pérez, "Partially exchangeable Markov chains and characterisation of multitype Lambda-coalescents", arXiv:2511.05435 (2025), Section 2.5 (Definition of multitype Λ-coalescents with multiple switching, Theorem 2.2), <https://doi.org/10.48550/arXiv.2511.05435>.
