# Coming down from infinity for the seed bank coalescent with simultaneous switching

**Model.** Fix $c,K\in(0,\infty)$ — or $c=0$ in parts 2 and 3 below — and finite measures $\Lambda,\bar\Lambda$ on $[0,1]$ without atom at $0$. The *seed bank $k$-coalescent with simultaneous switching* is the Markov chain on partitions of $\{1,\dots,k\}$ whose blocks carry a mark $a$ (active) or $d$ (dormant), with transitions from a marked partition $\pi$, where $|\pi|$ is the number of active blocks of $\pi$ in the $a\to d$ rates and the number of dormant blocks in the $d\to a$ rates (each eligible block takes part independently with probability $z$; the source writes $|\pi|$ for the number of all blocks, but its block-counting rates use the active and dormant counts):

- two active blocks merge at rate $1$;
- exactly one block switches $a\to d$ at rate $c+\int z(1-z)^{|\pi|-1}\,z^{-1}\Lambda(dz)$, and $d\to a$ at rate $cK+\int z(1-z)^{|\pi|-1}\,z^{-1}\bar\Lambda(dz)$;
- exactly $k\ge2$ given blocks switch $a\to d$ simultaneously at rate $\int z^k(1-z)^{|\pi|-k}\,z^{-1}\Lambda(dz)$, and $l\ge2$ given blocks switch $d\to a$ at rate $\int z^l(1-z)^{|\pi|-l}\,z^{-1}\bar\Lambda(dz)$.

These rates are consistent, so the chains have a projective limit, the seed bank coalescent with simultaneous switching ($\Lambda=\bar\Lambda=0$ recovers the ordinary seed bank coalescent). Its block-counting process is $(N_t,M_t)$ (active, dormant). The forward model is the moment dual

$$
\begin{aligned}
dX_t&=c(Y_t-X_t)\,dt+\sqrt{X_t(1-X_t)}\,dB_t+\int_{[0,1]}z\,(Y_{t-}-X_{t-})\,N^F(dt,dz),\\
dY_t&=cK(X_t-Y_t)\,dt+\int_{[0,1]}z\,(X_{t-}-Y_{t-})\,N^D(dt,dz),
\end{aligned}
$$

with independent Poisson point processes $N^F,N^D$ of intensities $dt\otimes z^{-1}\Lambda(dz)$ and $dt\otimes z^{-1}\bar\Lambda(dz)$, the scaling limit of Wright–Fisher models in which a random fraction $z$ of the population enters or leaves the seed bank at once.

**Theorem (coming down from infinity).** Let $Y$ have law $\Lambda/\Lambda([0,1])$.

1. If $\bar\Lambda(\{1\})=0$, the block-counting process started from $(n,\infty)$, $n\in\mathbb N_0\cup\{\infty\}$, stays infinite for all times.
2. Started from $(\infty,m)$, $m\in\mathbb N_0$, it comes down from infinity instantaneously if $\mathbb E[-\log Y]<\infty$ and $c=0$; if $\mathbb E[-\log Y]=\infty$ or $c>0$ it stays infinite for all times.
3. If $\bar\Lambda(\{1\})>0$, $c=0$ and $\mathbb E[-\log Y]<\infty$, then started from $(n,\infty)$ it comes down from infinity after a finite time, but not instantaneously.

## Depends on

- [Seed-bank coalescent](../seed-bank-coalescent-active-dormant-lineages.md)
- [The seed-bank coalescent does not come down from infinity](../the-seed-bank-coalescent-does-not-come-down-from.md)

## Expansion

The switching measure is $z^{-1}\Lambda(dz)$, with a singularity of order at most one at $0$, unlike the $z^{-2}\Lambda(dz)$ of $\Lambda$-coalescents: a merger needs two lineages to be visible, whereas a switch is visible when a single lineage moves. Dormant blocks never merge, so infinitely many dormant lineages can only disappear by waking up; this requires a simultaneous awakening of all dormant lineages, i.e. an atom of $\bar\Lambda$ at $1$, which explains parts 1 and 3. Starting with infinitely many active lineages, Kingman-type merging brings their number down instantly unless lineages escape to the seed bank too fast: with $c>0$ infinitely many single lineages escape at once, and with $c=0$ the simultaneous-switching events remove a positive fraction $z$ of active lineages at rate $z^{-1}\Lambda(dz)$, which is harmless exactly when the logarithmic moment $\mathbb E[-\log Y]$ is finite. With $c>0$ and no simultaneous switching one recovers the known fact that the ordinary seed bank coalescent does not come down from infinity.

## Sources

- Jochen Blath, Noemi Kurt, "Population genetic models of dormancy", in *Probabilistic Structures in Evolution* (E. Baake and A. Wakolbinger, eds.), EMS Series of Congress Reports, EMS Press (2021), 247–266, <https://doi.org/10.4171/ECR/17-1/12>; preprint arXiv:2012.00810 (2020), section "Seed banks with simultaneous switching": definition of the seed bank coalescent with simultaneous switching, remark on the switching measure, convergence to the jump diffusion with duality, and coming-down-from-infinity theorem, <https://doi.org/10.48550/arXiv.2012.00810>.
- Jochen Blath, Adrián González Casanova, Noemi Kurt and Maite Wilke-Berenguer, "The seed bank coalescent with simultaneous switching", *Electronic Journal of Probability* 25 (2020), 1–21, <https://doi.org/10.1214/19-EJP401> (original proofs).
