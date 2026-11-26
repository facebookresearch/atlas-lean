# SMCSD hidden Markov model with variable population size

**Setting.** Let $O_n$ be $n$ observed haplotypes over loci $\ell = 1, \dots, L$, and let $\alpha$ be a new haplotype. Population size history is $\lambda(t) = N(t)/N_{\mathrm{ref}}$ with $t$ in units of $2N_{\mathrm{ref}}$ generations; for the boundary $b = (\ell-1,\ell)$ let $\rho_b = 4N_{\mathrm{ref}}r_b$, and at locus $\ell$ let $\theta_\ell = 4N_{\mathrm{ref}}\mu_\ell$ with mutation matrix $P^{(\ell)}$. In the *trunk genealogy* approximation the lineages of $O_n$ neither mutate, recombine nor coalesce but extend to infinity, and the new lineage is absorbed into the trunk at total rate $n/\lambda(t)$, mutates at rate $\theta_\ell$ and recombines at rate $\rho_b$.

**Hidden Markov model.** The hidden state at locus $\ell$ is $S_\ell = (T_\ell, H_\ell)$, the absorption time and the absorbing haplotype, and the emission is the allele $\alpha[\ell]$. With $n_h$ the multiplicity of haplotype $h$ in $O_n$:

- *Initial density.*

$$\zeta^{(\lambda)}(t,h) = \frac{n_h}{\lambda(t)}\exp\!\Big(-n\int_0^t\frac{d\tau}{\lambda(\tau)}\Big),$$

so the absorbing haplotype is drawn in proportion to $n_h$, independently of the absorption time.
- *Transition density* from $(t,h)$ to $(t',h')$, writing $\zeta^{(\lambda)}(\tau) = \sum_h\zeta^{(\lambda)}(\tau,h)$:

$$\phi^{(\lambda)}(t',h' \mid t,h) = e^{-\rho_bt}\,\delta_{(t,h),(t',h')} + \int_0^{\min(t,t')}\rho_b e^{-\rho_bt_r}\,\frac{\zeta^{(\lambda)}(t',h')}{\int_{t_r}^\infty\zeta^{(\lambda)}(\tau)\,d\tau}\,dt_r .$$

- *Emission probability.*

$$\xi^{(\lambda)}(a \mid t,h) = e^{-\theta_\ell t}\sum_{m=0}^\infty\frac{(\theta_\ell t)^m}{m!}\big[(P^{(\ell)})^m\big]_{h[\ell],a}.$$

The forward algorithm over these densities gives the sequentially Markov conditional sampling probability $\hat\pi^{(\lambda)}_{\mathrm{SMC}}(\alpha \mid O_n)$; discretizing time into intervals turns the densities into matrices whose entries depend on $\lambda$ only through interval integrals, at cost quadratic in $n$.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](../../two-locus-coalescent/sequentially-markov-coalescent-smc-smc-pairwise.md)
- [Tavaré's formula](../../ancestral-lineage-counting-and-tavar-s-formula/exp-block-counting-generator-apply.md)

## Expansion

The absorption time has hazard $n/\lambda(t)$, the variable-size coalescent rate against $n$ static trunk lineages, which gives the survival factor $\exp(-n\int_0^t d\tau/\lambda)$, and the trunk lineage is chosen uniformly, which gives the factor $n_h$ for the haplotype. Along the sequence, a recombination at time $t_r$ below the current absorption time (rate $\rho_b$ on a lineage of length $t$) frees the lineage, which is then re-absorbed after $t_r$ according to the initial law conditioned on not having been absorbed before $t_r$, which is the ratio in the transition density. Mutations along the lineage of length $t$ form a Poisson process of rate $\theta_\ell$, which gives the emission. The rates $\theta_\ell$ and $\rho_b$ are twice those of an ordinary lineage, the correction that makes the trunk approximation accurate at equilibrium. For $n = 1$ the model is a pairwise SMC with variable size, close to PSMC.

## Sources

- S. Sheehan, K. Harris and Y. S. Song, "Estimating variable effective population sizes from multiple genomes: a sequentially Markov conditional sampling distribution approach", Genetics 194 (2013), Equations (1)–(5) and the section "Discretizing the State Space", <https://doi.org/10.1534/genetics.112.149096> (PMC3697970).
