# Labeled paintbox characterization of labeled exchangeable partition probability functions

**Labeled partitions and transition pairs.** Fix a finite label (type) set $E = [d]$. A labeled partition of $[n]$ is a set partition whose blocks each carry a label in $E$. A transition pair $(\Pi, \tau)$ is a pair of random labeled partitions of $\mathbb N$ in which $\tau$ consists of singletons, with infinitely many of each label, and has a regular conditional law $P_\pi = P(\,\cdot \mid \tau = \pi)$. Think of $\tau$ as an initial configuration of typed lineages and $\Pi$ as the result of a random mutation and coalescence mechanism. The pair is *jointly exchangeable* if $(\sigma\Pi, \sigma\tau) \overset d= (\Pi, \tau)$ for every finite permutation $\sigma$. It is *equivariant* if $P_\pi(\sigma\Pi \in \cdot) = P_{\sigma\pi}(\Pi \in \cdot)$. It is *consistent* if $\rho_n\Pi$ is conditionally independent of the label of $n+1$ in $\tau$ given $\rho_n\tau$, where $\rho_n$ restricts to $[n]$.

**Labeled paintbox.** The parameter space $\square$ consists of pairs $(q, x)$. Here $q = (q_{k,l})$ is a column-stochastic matrix of mutation probabilities from type $l$ to type $k$, and $x = (x_{k,l,s})_{s\ge1}$ are ranked coalescence frequencies, with $\sum_s x_{k,l,s} \le 1$ and $x_{k,l,s} = 0$ whenever $q_{k,l} = 0$. The labeled paintbox partition $R(q,x)$ colors each type-$l$ individual independently with a point of $(0, d]$. Its $k$-blocks are the individuals that hit the same atom in $(k-1, k]$. For a pair $(\eta, \pi')$ described by a tensor $T$, its finite-dimensional laws are $P_\pi(\rho_nR(q,x) = \pi') = g_T(q)\,f_T(x)$. Here $g_T(q) = \prod_{k,l}q_{k,l}^{i_{k,l}}$ is the mutation probability, and $f_T(x)$ is the probability that the mutated lineages coalesce into exactly the blocks of $\pi'$. For one type, $f_T$ reduces to the integrand numerator of Schweinsberg's $\Xi$-coalescent rates.

**LEPPF.** A function $p : \mathcal T \to [0, \infty)$ on such tensors is a labeled exchangeable partition probability function if it satisfies normalization ($p(T_0) = 1$), symmetry under permuting the blocks of each type, and the multivariate consistency relation $p(T) = \sum_{k\in E}\big(p(T(k,l)) + \sum_{s=1}^{j_k}p(T(k,l,s))\big)$ for every $l \in E$ (add individual $n+1$ of type $l$ as a new $k$-block or into the $s$-th $k$-block).

**Theorem (representation of equivariant pairs).** $(\Pi, \tau)$ is equivariant if and only if, for $P_\tau$-almost every $\pi$, $\Pi$ is under $P_\pi$ a mixture $\int_\square P_\pi(R(q,x) \in \cdot)\,G_\pi(d(q,x))$ of labeled paintbox partitions, with $G_\pi = G_{\sigma\pi}$. The mixing variable is given by the limiting relative mutation and coalescence frequencies of $(\pi, \Pi)$, and $G_\pi$ is unique.

**Corollary (characterization of LEPPFs).** $p$ is an LEPPF if and only if there is a unique probability measure $G$ on $\square$ with
$$p(T) = \int_\square g_T(q)\,f_T(x)\,G(d(q,x)) \qquad \text{for all } T \in \mathcal T .$$

**Theorem (jointly exchangeable consistent pairs).** $(\Pi, \tau)$ is jointly exchangeable and consistent if and only if there are unique probability measures $F$ on the type-frequency simplex and $G$ on $\square$ with
$$P(\rho_n\Pi = \pi', \rho_n\tau = \pi) = \Big(\int\prod_{i=1}^n p_{t_i(\pi)}\,F(dp)\Big)\Big(\int_\square g_T(q)f_T(x)\,G(d(q,x))\Big).$$
Equivalently, such pairs correspond one-to-one to pairs (exchangeable law of $\tau$, LEPPF).

## Depends on

- [The paintbox representation for the partitions of Kingman's coalescent](../../coalescent-theory/partition-valued-kingman-coalescent/paintbox-representation-transported-to-coalescen.md)
- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescent-theory/coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

Given an equivariant pair and fixed $\pi$, attach to each block of $\Pi$ an independent uniform point in $(k-1, k]$ according to its label $k$. Read off, for each initial type $l$, the sequence of points carried by the type-$l$ individuals of $\pi$. Equivariance makes this array separately exchangeable, so de Finetti's theorem for separately exchangeable sequences gives random directing measures $(\nu_l)_{l\in E}$. Given them, $\Pi$ is the labeled paintbox $R(L(\nu))$. For an LEPPF, the consistency relation lets Kolmogorov's extension build a kernel whose transition pair is equivariant, and the representation yields $G$. Under consistency the conditional law cannot depend on unseen labels, so $G_\pi$ is the same $G$ for all $\pi$, which produces the product form $F \otimes G$. This is the multitype analogue of Kingman's paintbox theorem and underlies multitype $\Xi$-coalescents arising from multitype Cannings models.

## Sources

- M. Flamm, M. Möhle, "A paintbox characterization of labeled partitions", arXiv:2610.29824 (2026), Definitions 2.1, 3.2, 3.5, 3.9 and 4.1, Proposition 3.7, Remark 3.8, Theorem 3.14, Corollary 3.18, Theorem 4.4, Theorem 5.1, Corollary 5.2, <https://doi.org/10.48550/arXiv.2610.29824>.
