# Asymptotic total, active and inactive branch lengths of the seed-bank coalescent

**Model.** The seed-bank $n$-coalescent with deactivation intensity $c_1 > 0$ and activation intensity $c_2 > 0$ is a Markov chain on partitions of $[n]$ whose blocks are flagged *active* (plants) or *dormant* (seeds). Each pair of active blocks merges at rate $1$, an active block becomes dormant at rate $c_1$, and a dormant block becomes active at rate $c_2$; dormant blocks do not merge. (In the notation $c$, $K$ of the seed-bank coalescent article, $c_1 = c$ and $c_2 = cK$.) Its block-counting process $(N_n(t), M_n(t))$ (active, dormant) jumps from $(i,j)$ to $(i-1,j)$ at rate $\binom{i}{2}$, to $(i-1,j+1)$ at rate $c_1 i$, and to $(i+1,j-1)$ at rate $c_2 j$. Start with $n$ active blocks and no seeds. Let $A_n$, $I_n$ and $L_n = A_n + I_n$ be the total active, inactive and total branch lengths of the genealogical tree.

**Theorem.** As $n \to \infty$, in probability,

$$\frac{A_n}{\log n} \to 2, \qquad \frac{I_n}{\log n} \to \frac{2c_1}{c_2}, \qquad \frac{L_n}{\log n} \to 2\Big(1 + \frac{c_1}{c_2}\Big).$$

Consequently, if mutations fall at rate $\mu$ along all branches, the number of segregating sites $S_n$ satisfies $S_n / \log n \to 2\mu(1 + c_1/c_2)$ in probability.

**Early phases.** Let $\gamma_n$ be the time of the first deactivation and $\theta_n$ the first time a dormant lineage reactivates. Then $N_n(\gamma_n)/n \to Y \sim \mathrm{Beta}(2c_1,1)$ and $n\gamma_n \to \Gamma = 2(1-Y)/Y$ in distribution, with density $f_\Gamma(x) = c_1\big(\frac{2}{2+x}\big)^{2c_1+1}$ on $x\ge 0$. At the first reactivation, $N_n(\theta_n)/\log n \to Z$, a Fréchet variable with $\mathbb{P}(Z \le z) = e^{-4c_1c_2/z}$; $M_n(\theta_n)/\log n \to 2c_1$ in probability; and $\theta_n\log n \to T \sim \mathrm{Exp}(2c_1c_2)$ in distribution.

## Depends on

- [Number of segregating sites under infinite-sites mutation](../../poisson-mutation-on-the-kingman-genealogy/seg-sites.md)
- [Infinite-sites mutation on a finite genealogy](../../poisson-mutation-on-the-kingman-genealogy/branch-mutation-kernel.md)
- [Seed-bank coalescent](../seed-bank-coalescent/seed-bank-coalescent-active-dormant-lineages.md)

## Proof depends on

## Expansion

Kingman's coalescent has total length $\sim 2\log n$, and the active part of the seed-bank tree has the same leading order: most active length accrues while there are many active lineages, when coalescence (rate $\binom{i}{2}$) beats deactivation (rate $c_1 i$). Every unit of active branch length produces deactivations at rate $c_1$, and each dormant spell lasts a mean time $1/c_2$, so the dormant length is about $c_1/c_2$ times the active length, giving $I_n \sim (2c_1/c_2)\log n$. The early-phase limits come from coupling with a pure coalescence-deactivation chain: the first reactivation happens only after about $2c_1\log n$ seeds have accumulated, at time of order $1/\log n$. Seed banks thus inflate the number of segregating sites by the factor $1 + c_1/c_2$ at leading order.

## Sources

- Adrián González Casanova, Lizbeth Peñaloza and Arno Siri-Jégousse, "The shape of a seed bank tree", arXiv:2001.04500 (2020), Theorem 1.1, Corollary 1.2, Propositions 2.1, 2.2 and 3.1, Theorems 4.1 and 4.2, <https://doi.org/10.48550/arXiv.2001.04500>; published in *Journal of Applied Probability* 59(3) (2022) 631–651, <https://doi.org/10.1017/jpr.2021.79>. Locators follow arXiv v2.
