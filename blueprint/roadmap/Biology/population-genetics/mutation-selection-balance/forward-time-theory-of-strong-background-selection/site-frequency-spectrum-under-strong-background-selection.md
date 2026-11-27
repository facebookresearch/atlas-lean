# Site frequency spectrum under strong background selection

In the model of [lineage trajectories under linked deleterious mutations](lineage-trajectories-under-linked-deleterious-mutations.md) (population size $N$, deleterious mutation rate $U_d \ll 1$ per locus, cost $s \ll 1$ per mutation, $\lambda = U_d/s$, no recombination), let neutral mutations arise at rate $U_n$ per individual per generation and let $p(f)$ be the expected number of neutral polymorphisms at population frequency $f$ in steady state. Assume strong selection, $N s e^{-\lambda} \gg 1$, so that deleterious alleles essentially never fix, and write $\sigma = \sqrt{U_d s}$ for the standard deviation of fitness in the population.

**Weak load ($\lambda \ll 1$).** To leading order in $\lambda$, background selection has no effect: $p(f) \approx 2 N U_n / f$, the neutral spectrum of a population of census size $N$.

**Strong load ($\lambda \gg 1$).** The spectrum has five regimes:

$$p(f) \approx \begin{cases}
\dfrac{2 N U_n}{f}, & f \ll \dfrac{1}{N\sigma},\\[2ex]
\dfrac{N U_n}{N s f^2 \sqrt{\lambda \,\log_\lambda\!\left(\dfrac{e^{\lambda}}{N s f}\right)}}, & \dfrac{1}{N\sigma} \ll f \ll \dfrac{e^{\lambda}}{N s},\\[2ex]
\dfrac{2 N U_n e^{-\lambda}}{f}, & \dfrac{e^{\lambda}}{N s} \ll f \ll 1 - \dfrac{e^{\lambda}}{N s},\\[2ex]
\dfrac{N U_n}{N s (1-f) \,\log_\lambda\!\left(\dfrac{e^{\lambda}}{N s (1-f)}\right)}, & \dfrac{1}{N\sigma} \ll 1-f \ll \dfrac{e^{\lambda}}{N s},\\[2ex]
\dfrac{2 N U_n}{f}, & 1 - f \ll \dfrac{1}{N\sigma},
\end{cases}$$

where $\log_\lambda$ is the logarithm to base $\lambda$ and the second line holds up to a constant factor.

So the spectrum is neutral with the reduced size $N_e = N e^{-\lambda}$ only for $1/(N s e^{-\lambda}) < f < 1 - 1/(N s e^{-\lambda})$. Below that window there is a large excess of rare alleles over the $N_e$ prediction (falling off faster than $1/f$ from the census-size line at $f \approx 1/(N\sigma)$), and above it the spectrum rises again to the census-size line, so it is non-monotone. Summary statistics of the spectrum therefore start to deviate from the reduced-$N_e$ neutral expectation in samples larger than about $N s e^{-\lambda}$ ("$N_e s$") individuals, but not in smaller samples. Whenever pairwise diversity is reduced at all ($\pi/\pi_0 < 1$, i.e. McVicker's $B < 1$), these distortions are present.

## Proof sketch

As for an isolated locus (Ewens 1963), $p(f)$ is proportional to the rate at which mutations reach frequency $f$ times the time they spend near $f$. At the extremes ($f$ or $1-f$ below $1/(N\sigma)$) drift dominates the linked fitness variation of a typical allele, so the census-size spectrum holds; at the high end this also follows because neutral alleles enter the near-fixation regime at the unchanged rate $N U_n \cdot 1/N$. In the middle window both the neutral allele and the wild type are in their own mutation–selection balance, and their frequency fluctuations copy the neutral fluctuations of the $N e^{-\lambda}$ mutation-free individuals, giving the $N_e = N e^{-\lambda}$ spectrum. Between $1/(N\sigma)$ and $e^{\lambda}/(Ns)$ only lineages founded in classes $k \le k_c(f)$ with $k_c(f) + 1 \approx \log_\lambda\!\big(1/(N s e^{-\lambda} f)\big)$ can reach frequency $f$, and selection smooths out fluctuations of the most-fit class on time scales shorter than $1/s$, which produces the steep fall-off. Near fixation, neutral alleles that have fixed within the most-fit class behave as if positively selected (see the effective selection coefficient), which produces the high-frequency excess. The paper joins the piecewise forms with fitted $O(1)$ constants and checks them against Wright–Fisher simulations.

## Depends on

- [Lineage trajectories under mutation–selection balance at a non-recombining locus](lineage-trajectories-under-linked-deleterious-mutations.md)
- [Background selection reduces the effective size to the mutation-free class](../background-selection-deterministic-reduction-fac.md)
- [Neutral Poisson random field density](../../diffusion-theory/poisson-random-field-model/prf-density-zero.md)

## Proof depends on

- [Effective positive selection on neutral alleles near fixation under background selection](effective-selection-on-neutral-alleles-near-fixation.md)

## Sources

- I. Cvijović, B. H. Good and M. M. Desai, "The effect of strong purifying selection on genetic diversity", Genetics 209 (2018), 1235–1278, Model and Results (Equations 1–2), the site-frequency-spectrum analysis (Equations 30, 36–37, 41) and Figures 1–3, <https://doi.org/10.1534/genetics.118.301058> (PMC6063222). The second regime (Equation 2, second line, and Equation 41) and $\sigma = \sqrt{U_d s}$ are cited from the journal version; the PMC rendering drops their square roots.
