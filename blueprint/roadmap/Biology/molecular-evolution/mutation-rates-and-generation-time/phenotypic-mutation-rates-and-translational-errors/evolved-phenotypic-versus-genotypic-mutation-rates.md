# Evolved phenotypic versus genotypic mutation rates under Haldane's principle

Consider a large asexual population in which a cell with genotypic mutation rate $\mu$ and phenotypic mutation rate $u$ (both per codon) has mean fitness

$$\bar f(\mu,u)=(1-\mu)^n\bigl[1-\bar\eta(u)\bigr],\qquad n=\sum_i n_i,$$

where $n$ is the effective genome size in codons, $\bar\eta(u)$ is the expected fitness cost of synthesizing abnormal proteins, with $\bar\eta(0)=0$, and $(1-\mu)^n$ is the mutation load at mutation-selection balance. Suppose mutations that change $\mu$ and $u$, mostly upward, arise at rates $\pi_\mu$ and $\pi_u$. Treating each rate as a trait at mutation-selection balance and applying Haldane's principle (mean fitness is reduced by the rate of mutation away from the optimum, independently of the mutants' fitnesses) gives

$$\hat\mu\approx\frac{\pi_\mu}{n},\qquad \bar\eta(\hat u)=\pi_u,\qquad \hat\mu\,n\approx\bar\eta(\hat u)\,\frac{\pi_\mu}{\pi_u}.$$

If the cost is linear in the amount of abnormal protein, $\eta(x)=c\,x$, and the linear load approximation $\bar x\approx u\sum_i n_i^2y_i$ holds, then

$$\hat u\approx\frac{\pi_u}{c\sum_i n_i^2y_i},\qquad\frac{\hat u}{\hat\mu}\approx\frac{\sum_i n_i}{c\sum_i n_i^2y_i}\,\frac{\pi_u}{\pi_\mu}.$$

## Depends on

- [Expected abnormal-protein load under error-prone protein synthesis](expected-abnormal-protein-load-under-error-prone-synthesis.md)
- [Mutation-rate modifiers and the drift-barrier hypothesis](../../mutation-rate-modifiers-and-the-drift-barrier-hy.md)

## Expansion

Haldane's principle says that at mutation-selection balance mean fitness equals the optimum's fitness times one minus the mutation rate away from it, to first order. For the trait $u$ at fixed $\mu$ the optimum is $u=0$ with fitness $\bar f(\mu,0)=(1-\mu)^n$, so $\bar f(\mu,\hat u)\approx\bar f(\mu,0)(1-\pi_u)$, which gives $\bar\eta(\hat u)=\pi_u$. For $\mu$ the same argument gives $(1-\hat\mu)^n\approx1-\pi_\mu$, hence $n\hat\mu\approx\pi_\mu$. The ratio formula follows by dividing, and the linear-cost version by substituting $\bar\eta(u)=c\,\bar x(u)\approx c\,u\sum_i n_i^2y_i$. The source notes that the general theory and its numerics make these approximations slight overestimates, and that in finite populations selection becomes ineffective once the costs fall below a drift threshold, so simulated equilibria move less with $\pi_u$ and $\pi_\mu$ than the formulas predict. With the yeast effective genome $n=2.81\times10^6$, $\pi_u=\pi_\mu$ and $c=10^{-10}$, the ratio formula gives $\hat u/\hat\mu\approx2.10\times10^3$, close to Wright–Fisher simulations; for very small $c$ the formula fails because $\bar x$ leaves its linear regime.

## Sources

- M. Willensdorfer, R. Bürger and M. A. Nowak, "Phenotypic mutation rates and the abundance of abnormal proteins in yeast", PLoS Computational Biology 3 (2007), e203, Results ("The Model", Equations (1) to (3); "Evolving Mutation Rates", Equations (4) to (6) and (9); "Simulating the Evolution of Mutation Rates") and the appendix section "Mutation Rates at Equilibrium", Equations (23) and (24), <https://doi.org/10.1371/journal.pcbi.0030203> (PMC2082502).
