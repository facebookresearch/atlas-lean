# Stationary law of the ancestral recombination graph under strong recombination

**Model.** Fix distinct loci $z=\{z_0,\dots,z_n\}\subset\mathbb{R}$ and a recombination rate $\rho>0$. The ancestral recombination graph $\Gamma^{\rho,z}$ is the continuous-time Markov chain on the set $\mathcal P_z$ of partitions of $z$ with transitions

- *coagulation*: any two blocks merge, at rate $1$;
- *fragmentation*: a block with elements $z_{i_1}<\dots<z_{i_k}$ splits into $\{z_{i_1},\dots,z_{i_j}\}$ and $\{z_{i_{j+1}},\dots,z_{i_k}\}$ ($1\le j<k$) at rate $\rho\,(z_{i_{j+1}}-z_{i_j})$.

It has a unique invariant law $\mu^{\rho,z}$, and $\Gamma^{R,z}=\Gamma^{1,Rz}$ in distribution, so large $\rho$ is equivalent to widely spaced loci. There is a unique càdlàg process $\Pi^\rho$ on right-continuous locally finite partitions of $\mathbb{R}_+$ whose restriction to every finite $z$ is $\Gamma^{\rho,z}$; it has a unique invariant law $\mu^\rho$ whose restriction to $z$ is $\mu^{\rho,z}$, and $h_\lambda\star\mu^\rho=\mu^{\lambda\rho}$ for the dilation $h_\lambda(x)=\lambda x$.

**Coalescence scenarios.** A partition has order $r$ if it has $n+1-r$ blocks; the finest partition $\pi_0$ has order $0$. The cover length of $\pi$ is $C(\pi)=\sum_{\text{blocks }b}\max_{x,y\in b}|x-y|$ (the total fragmentation rate out of $\pi$ divided by $\rho$). A coalescence scenario of order $r$ is a sequence $s=(s_0,\dots,s_r)$ with $s_0=\pi_0$ and $s_k$ obtained from $s_{k-1}$ by one coagulation; its energy is $E(s)=\prod_{i=1}^r C(s_i)$. For $\pi$ of order $r\ge1$ let $\mathcal S(\pi)$ be the scenarios ending at $\pi$ and

$$
F(\pi)=\sum_{s\in\mathcal S(\pi)}\frac{1}{E(s)}.
$$

**Theorem.** Let $\alpha=\min_{i\ne j}|z_i-z_j|>0$. For every $n$ there is a function $f^n$ with $f^n(x)\to0$ as $x\to\infty$, independent of $z$ and $\rho$, such that for all $\rho>0$, $k\in\{1,\dots,n\}$ and every partition $\pi_k$ of order $k$,

$$
\Bigl|\mu^{\rho,z}(\pi_k)-\frac{F(\pi_k)}{\rho^k}\Bigr|\le f^n(\alpha\rho)\,\frac{F(\pi_k)}{\rho^k}.
$$

## Expansion

When $\alpha\rho$ is large, fragmentation dominates and at stationarity the chain sits mostly at the finest partition, making short excursions in which loci are transiently brought together. By the renewal (cycle) formula, $\mu^{\rho,z}(\pi)$ is the expected time spent at $\pi$ per excursion divided by the mean excursion length. Reaching an order-$k$ partition requires $k$ successive coagulations, each at rate $1$, racing against fragmentation at rate $\rho\,C(s_i)$ out of the intermediate state; the probability of following scenario $s$ is therefore close to $\prod_i 1/(\rho C(s_i))$, and summing over scenarios and multiplying by the holding time $1/(\rho C(\pi))$ gives $F(\pi)/\rho^k$ to leading order. Paths that wander off the direct scenarios cost extra factors of order $1/(\alpha\rho)$, which produces the uniform relative error $f^n(\alpha\rho)$. Because blocks need not be intervals ("trapped material"), $C(\pi)$ can exceed the diameter of $z$.

## Sources

- Amaury Lambert, Verónica Miró Pina and Emmanuel Schertzer, "Chromosome painting: How recombination mixes ancestral colors", *Ann. Appl. Probab.* 31(2) (2021), 826–864. <https://doi.org/10.1214/20-AAP1606>
- Preprint version (the locators in this item follow its numbering): Amaury Lambert, Verónica Miró Pina, Emmanuel Schertzer, *Chromosome painting: how recombination mixes ancestral colors*, arXiv (2018). Theorem 1.1 (the half-line partitioning process), Theorem 1.2 (invariant measure), Theorem 1.3 (approximation of the stationary distribution), Proposition 3.4 (scaling). <https://doi.org/10.48550/arXiv.1807.09116>
