# Density of a Tajima's genealogy under a variable population size

A *Tajima's genealogy* of $n$ samples is the pair $g^{T} = (F, \mathbf t)$ of a ranked tree shape $F$ with $c$ cherries and the vector of coalescence times $\mathbf t = (t_n, \dots, t_2)$ measured from the present into the past, where the sample has exactly $k$ ancestors during $[t_{k+1}, t_k)$ and $t_{n+1} = 0$. Coarsening Kingman's genealogy to its ranked tree shape does not change the law of the intercoalescent times, so with $C_k = \binom{k}{2}$ and effective size trajectory $(N(t))_{t \ge 0}$,

$$\Pr\bigl(t_k - t_{k+1} \mid t_{k+1}, N(\cdot)\bigr) = \frac{C_k}{N(t_k)} \exp\left[ - \int_{t_{k+1}}^{t_k} \frac{C_k}{N(t)}\, dt \right],$$

and the whole genealogy has density

$$\Pr\bigl(g^{T} \mid N(\cdot)\bigr) = \frac{2^{\,n-c-1}}{(n-1)!} \prod_{k=2}^{n} \frac{C_k}{N(t_k)} \exp\left[ - \int_{t_{k+1}}^{t_k} \frac{C_k}{N(t)}\, dt \right].$$

The density factors into a combinatorial term free of $N(\cdot)$ and a product of interval terms depending only on the coalescence times.

## Depends on

- [Probability of a ranked tree shape under the coalescent](probability-of-a-ranked-tree-shape.md)
- [The time-changed coalescent as the limit of a Wright–Fisher model of varying size](../../site-frequency-spectrum-under-variable-populatio/derivation-of-the-time-changed-coalescent-from-a.md)

## Proof depends on

- [Holding times and jump chain of Kingman's n-coalescent are independent](../../partition-valued-kingman-coalescent/holding-times-and-jump-chain-of-kingman-s-n-coal.md)

## Expansion

The interval density is the standard inhomogeneous-rate first-event density of the coalescent with variable size: while $k$ ancestors remain, pairs coalesce at instantaneous rate $C_k/N(t)$, which gives the hazard form above. Independence of the topology from the times holds because the merging pair is chosen uniformly among pairs, so the product of the two factors is the joint law. The factorization is what makes the ranked tree shape a legitimate reduction of the hidden state in Bayesian inference: placing a log-Gaussian process prior $\log N(t) \sim \mathcal{GP}(0, C(\tau))$ with, for instance, a Brownian-motion covariance $\operatorname{Cov}[\log N(t_i^*), \log N(t_j^*)] = \tau \min(t_i^*, t_j^*)$ and a Gamma prior on the precision $\tau$, the posterior over $(N(\cdot), g^T, \tau)$ can be explored by Hamiltonian Monte Carlo for the continuous coordinates together with Metropolis–Hastings moves on the ranked tree shape, in a state space superexponentially smaller than the space of labelled genealogies.

## Sources

- J. A. Palacios, A. Véber, L. Cappello, Z. Wang, J. Wakeley, S. Ramachandran, "Bayesian estimation of population size changes by sampling Tajima's trees", *Genetics* 213 (2019), 967–986, <https://doi.org/10.1534/genetics.119.302373> (PMC6827370). Materials and Methods, "Tajima's genealogies" and "Bayesian inference of the effective population size trajectory", Equations (2), (3), (5) and (8).
