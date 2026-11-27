# Block frequency of a fixed individual in Ξ-coalescents with dust

**Setting.** Let $\Xi$ be a finite measure on the simplex $\Delta=\{x=(x_1,x_2,\dots):x_1\ge x_2\ge\cdots\ge0,\ \sum_ix_i\le1\}$ and $(x,x)=\sum_ix_i^2$. The $\Xi$-coalescent *has dust* if $\sum_ix_i\,\Xi(dx)/(x,x)$ is a finite measure, and set

$$\mu_{-1}=\int_\Delta\sum_{i\ge1}x_i\,\frac{\Xi(dx)}{(x,x)}<\infty .$$

It *stays infinite* if it has infinitely many blocks at every time almost surely. Let $f_1(t)$ be the asymptotic frequency of the block containing individual $1$ at time $t$ (the relative size of the clade of $1$ in an infinite sample).

**Theorem.** In a $\Xi$-coalescent with dust that stays infinite:

1. $(f_1(t))_{t\ge0}$ is an increasing pure-jump càdlàg process with $f_1(0)=0$, $f_1(t)<1$ for all $t>0$ and $f_1(t)\to1$ as $t\to\infty$, almost surely; it has infinitely many jumps, and the waiting times between successive jumps are independent $\mathrm{Exp}(\mu_{-1})$ random variables.
2. Its jump chain has a stick-breaking form

$$f_1[k]=\sum_{i=1}^kX_i\prod_{j=1}^{i-1}(1-X_j),$$

where the $X_j>0$ are pairwise uncorrelated with $\mathbb E X_j=\gamma=\Xi(\Delta)/\mu_{-1}$; consequently

$$\mathbb E\,f_1[k]=1-(1-\gamma)^k .$$

In general the $X_j$ are neither independent nor identically distributed.

Relatedly, for any $\Xi$-$n$-coalescent the external branch length of individual $1$ decreases in $n$ and converges in distribution to $\mathrm{Exp}(\mu_{-1})$; without dust ($\mu_{-1}=\infty$) it tends to $0$.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)
- [The Ξ-coalescent rate matrix on partitions of a finite sample](../../coalescents/xi-coalescent-partition-valued-ctmc-and-restrict.md)

## Expansion

With dust, $\Xi$ puts no mass on the zero sequence, and the coalescent can be built from a Poisson point process on $[0,\infty)\times\Delta$ with intensity $dt\otimes\Xi(dx)/(x,x)$ by paintbox colouring: at an atom $(t,x)$ each block independently joins group $i$ with probability $x_i$. Individual $1$'s block takes part in the event with probability $\sum_ix_i$, so its participation times form a Poisson process of rate $\mu_{-1}$, giving the exponential waiting times. At each participation it absorbs a fraction $X_k$ of the remaining dust mass $1-f_1(t-)$ (which stays positive because the coalescent stays infinite), and averaging over the colouring gives $\mathbb E X_k=\Xi(\Delta)/\mu_{-1}$; the correlations vanish but independence fails because the remaining blocks' structure is shared.

## Sources

- Fabian Freund, "Multiple-merger genealogies: models, consequences, inference", in *Probabilistic Structures in Evolution* (E. Baake and A. Wakolbinger, eds.), EMS Series of Congress Reports, EMS Press (2021), 179–202, <https://doi.org/10.4171/ECR/17-1/9>; preprint arXiv:2010.12271 (2020), section "Partition blocks and minimal observable clades", proposition on $f_1$ for $\Xi$-coalescents with dust (after Freund and Möhle, Thm. 1) and the external-branch limit $\mathrm{Exp}(\mu_{-1})$, <https://doi.org/10.48550/arXiv.2010.12271>.
- Fabian Freund and Martin Möhle, "On the size of the block of 1 for Ξ-coalescents with dust", *Modern Stochastics: Theory and Applications* 4 (2017), 407–425, <https://doi.org/10.15559/17-VMSTA92> (original proof).
