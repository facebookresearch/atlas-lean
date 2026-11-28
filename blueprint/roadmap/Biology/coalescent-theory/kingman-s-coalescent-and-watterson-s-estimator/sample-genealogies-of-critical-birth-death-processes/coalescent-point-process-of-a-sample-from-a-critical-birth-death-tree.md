# Coalescent point process of a sample from a critical birth–death tree

Consider a critical birth–death tree (birth and death rates both $1$) founded $Nt$ time units before the present. Each extant individual is sampled independently with probability $p/N$, time is rescaled by $1/N$, and the tree is conditioned on having exactly $n$ sampled individuals. Ordering the sample along the planar tree, the genealogy of the sample is encoded by its **coalescent point process**

$$\pi_n = \sum_{k=1}^{n-1} \delta_{(k/n,\, H_k)},$$

where $H_k$ is the divergence time (node depth) between the $k$-th and $(k+1)$-th sampled individuals. Write $P^t_n$ for the law with fixed time of origin $t$, $P^{(\infty)}_n$ for infinite time of origin, and $P^{(i)}_n$, $i \in \{0,1,2,\dots\}$, for a random time of origin with (possibly improper) prior density $g_i(x) = x^{-i}$; $i = 0$ is the uniform prior.

**Theorem (Achaz–Delaporte–Lambert, Theorem 2.1).** Under $P^t_n$, the node depths $H_1,\dots,H_{n-1}$ are independent and identically distributed with density

$$x \mapsto \frac{p}{(1+px)^2}\cdot\frac{1+pt}{pt}\, \mathbf 1_{(0,t)}(x).$$

So the sample genealogy is the genealogy of a critical birth–death process with rate $p$ conditioned on $n$ extant individuals at time $t$; the scaling $N$ drops out, while $p$ and $t$ both shape branch-length ratios.

**Proposition (Achaz–Delaporte–Lambert, Proposition 2.4).** Under $P^{(\infty)}_n$, the $H_k$ are i.i.d. with density $p/(1+px)^2$ on $(0,\infty)$.

**Proposition (Achaz–Delaporte–Lambert, Proposition 2.6).** Under $P^{(i)}_n$ with $0 \le i < n$, the law of the tree is the mixture of $P^t_n$ over the time of origin $T_{\mathrm{or}}$ with posterior density

$$h^{(i)}_n(t) = p\, n \binom{n-1}{i} \frac{(pt)^{n-i-1}}{(1+pt)^{n+1}}\, \mathbf 1_{t>0}.$$

**Propositions (moments of coalescence times; Achaz–Delaporte–Lambert, Propositions 2.5 and 2.9).** Let $T_{n,k}$ be the time to the $k$-th most recent common ancestor of the sample, the $k$-th largest of $H_1,\dots,H_{n-1}$. Under $P^{(\infty)}_n$ its $m$-th moment is finite if and only if $m \le k-1$, and then

$$E^{(\infty)}_n\big(T_{n,k}^m\big) = \frac{\binom{n-k+m-1}{m}}{p^m \binom{k-1}{m}}.$$

Under $P^{(i)}_n$ the $m$-th moment is finite if and only if $m \le k+i$; for the uniform prior and $m \le k$,

$$E^{(0)}_n\big(T_{n,k}^m\big) = \frac{\binom{n-k+m-1}{m}}{p^m \binom{k}{m}}.$$

## Expansion

The genealogy of the whole extant population of a birth–death tree is a coalescent point process with i.i.d. node depths whose tail is the probability that a subtree survives to the present; for the critical process with rate $1$ this tail is $1/(1+x)$. Bernoulli sampling with probability $p/N$ followed by time rescaling by $1/N$ produces again a coalescent point process with tail $1/(1+px)$, and conditioning on $n$ sampled individuals with origin at $t$ truncates the depths to $(0,t)$, which gives the stated density. Mixing over the prior $x^{-i}$ against the likelihood of $n$ samples yields the posterior $h^{(i)}_n$; the order statistics of i.i.d. depths with tail $1/(1+px)$ give the moment formulas, and the heavy tail explains which moments are infinite.

## Sources

- G. Achaz, C. Delaporte and A. Lambert, *Sample genealogy and mutational patterns for critical branching populations*, published as "Mutational pattern of a sample from a critical branching population", *Journal of Mathematical Biology* 73 (2016), 627–664, <https://doi.org/10.1007/s00285-015-0964-2>; preprint arXiv:1407.7720, <https://doi.org/10.48550/arXiv.1407.7720>.
