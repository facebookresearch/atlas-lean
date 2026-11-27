# Extinction process of alleles equals the Kingman block-counting process

**Setting.** Consider a Moran population of constant size $N$ in which every individual carries a distinct allele at time $0$. Every unordered pair $\{a,b\}$ of individuals has an independent rate-$1$ Poisson clock; when it rings, one of the two, chosen uniformly, gives birth to an offspring of its allele and the other dies (equivalently, every ordered pair $(a,b)$ has a rate-$1/2$ clock at which $a$ reproduces and $b$ dies). Define the **extinction process** and its jump times

$$\hat A^N_t = \#\{\text{alleles present at time } t\}, \qquad \hat T^{N,k} = \sup\{t > 0 : \hat A^N_t \ge k\}, \quad k \in \{2,\dots,N\},$$

so $\hat T^{N,2}$ is the fixation time. For the $N$-Kingman coalescent let $A^N_t$ be the number of ancestral lineages (blocks) at time $t$ and $T^{N,k} = \sup\{t > 0 : A^N_t \ge k\}$; $A^N$ is the pure-death process started at $N$ with rate $k(k-1)/2$ from $k$ to $k-1$.

**Theorem.** For every $N \in \mathbb{N}$, the forward-time extinction process $(\hat A^N_t)_{t\ge 0}$ and the backward-time block-counting process $(A^N_t)_{t\ge 0}$ are identical in law. In particular the loss of allelic diversity is a pure-death process with rates $k(k-1)/2$, and $\hat T^{N,k}$ has the law of $T^{N,k}$, a sum of independent exponentials with rates $j(j-1)/2$, $j = k, \dots, N$.

**Extension to $\Lambda$-Fleming–Viot populations.** For the $N$-particle $\Lambda$-Fleming–Viot process and its genealogy, the $\Lambda$-coalescent, the one-dimensional marginals agree: for every fixed $t > 0$, $A^N_t$ and $\hat A^N_t$ have the same law, and for every fixed $k$, $T^{N,k}$ and $\hat T^{N,k}$ have the same law. Equality of the whole processes is special to the binary (Kingman) case.

## Depends on

- [Holding times and jump chain of Kingman's n-coalescent are independent](../../../coalescent-theory/partition-valued-kingman-coalescent/holding-times-and-jump-chain-of-kingman-s-n-coal.md)

## Expansion

In the Moran model, conditionally on the current allele count $k$ and the allele sizes, the next event that removes an allele is a birth–death pair in which the dying individual is the last carrier of its allele. A martingale or exchangeability argument shows that, whatever the allele sizes, the rate at which the number of alleles drops is the same function of $k$ as the merger rate $k(k-1)/2$ of $k$ Kingman lineages after averaging over the uniform (Dirichlet) allele-size configuration, and this configuration is preserved at jump times. The block-counting process is classical: each of the $\binom{k}{2}$ pairs of lineages merges at rate $1$. For multiple-merger $\Lambda$-coalescents the allele-size configuration at extinction times is no longer independent of the past in the same way, so only fixed-time and fixed-level marginals coincide.

## Sources

- Guillaume Achaz, Amaury Lambert and Emmanuel Schertzer, "The sequential loss of allelic diversity", *Adv. Appl. Probab.* 50 (2018), 13-29. <https://doi.org/10.1017/apr.2018.67>
- Preprint version (the locators in this item follow its numbering): Guillaume Achaz, Amaury Lambert and Emmanuel Schertzer, "The sequential loss of allelic diversity", arXiv:1801.00683 (2018), Theorem 2.1 (binary case) and Theorem 3.1 (general $\Lambda$ case, part (2) due to Hénard), <https://doi.org/10.48550/arXiv.1801.00683>. The preprint's Section 2.1 gives every ordered pair a rate-$1$ clock, which makes each unordered pair resolve at rate $2$ and is off by a time factor of $2$ from the rates $k(k-1)/2$ in its (2.3); the model above uses the rate under which the stated identity holds (for $N=2$ both fixation times are exponential with rate $1$).
