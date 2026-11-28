# Coalescent point process and thinning simulation

Consider the coalescent with a deterministic effective population size trajectory $N_e(t) > 0$, time measured backwards from the present, for a sample of $n$ lineages all taken at time $t_n = 0$. With coalescent times $0 = t_n < t_{n-1} < \cdots < t_1$ and $C_k = \binom{k}{2}$, the conditional density of the next coalescent time is

$$
P(t_{k-1} \mid t_k) = \frac{C_k}{N_e(t_{k-1})} \exp\left\{-\int_{t_k}^{t_{k-1}} \frac{C_k}{N_e(u)}\,du\right\},
$$

so the joint density of the coalescent times is that of a point process with conditional intensity

$$
\lambda^*(t \mid t_k) = \binom{k}{2}\, N_e(t)^{-1}, \qquad t \in (t_k, t_{k-1}],\quad k = 2,\dots,n .
$$

For serially sampled (heterochronous) data the coefficient $\binom{k}{2}$ is replaced by $\binom{n_{i,k}}{2}$ on each subinterval between consecutive coalescent and sampling times, $n_{i,k}$ being the number of lineages present there.

**Thinning.** Suppose $1/N_e(t) \le \lambda$ for all $t$. Starting from $k = n$ and $t = t_n = 0$, repeatedly draw $E \sim \mathrm{Exponential}(C_k\lambda)$ and $U \sim \mathrm{Uniform}(0,1)$, set $t \leftarrow t + E$, and if $U \le 1/(\lambda N_e(t))$ set $k \leftarrow k-1$ and $t_k \leftarrow t$; stop when $k = 1$. This algorithm generates $t_n < t_{n-1} < \cdots < t_1$ with (Proposition 1, Appendix A)

$$
P(t_{k-1} > t \mid t_k) = \exp\left[-\int_{t_k}^{t} \frac{C_k}{N_e(x)}\,dx\right],
$$

that is, exactly the coalescent with population size trajectory $N_e$.

## Depends on

- [Log-likelihood of one coalescent interval in the skyline model](../skyline-log-lik.md)

## Expansion

Only the coalescent times carry information about $N_e$, and between events the process behaves like an inhomogeneous Poisson process of rate $C_k/N_e(t)$, so estimating $N_e$ is estimating a conditional intensity. The usual simulation method inverts the integrated intensity, which requires computing $\int C_k/N_e$; thinning instead proposes points from a homogeneous Poisson process of rate $C_k\lambda$ and accepts each with probability $1/(\lambda N_e(t))$, in the manner of Lewis–Shedler and Ogata thinning. Conditionally on $m$ proposals in $(t_k,t]$ the proposal times are uniform, each accepted with average probability $\frac{1}{\lambda(t-t_k)}\int_{t_k}^t N_e(x)^{-1}dx$, and summing over the Poisson number of proposals gives the stated survival function. Thinning needs only pointwise evaluation of $N_e$, so it also applies when $N_e$ is random, which is what makes it useful for data augmentation.

## Sources

- Julia A. Palacios, Vladimir N. Minin, Gaussian process-based Bayesian nonparametric inference of population trajectories from gene genealogies, *Biometrics* 69 (2013), 8–18, <https://doi.org/10.1111/biom.12003>; preprint arXiv:1112.4138, <https://doi.org/10.48550/arXiv.1112.4138>.
