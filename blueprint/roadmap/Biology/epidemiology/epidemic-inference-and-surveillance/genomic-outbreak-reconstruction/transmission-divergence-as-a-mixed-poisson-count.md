# Transmission divergence as a mixed Poisson count

The transmission divergence $K$ of a transmission pair is the number of mutations separating pathogen genomes sampled from the infector and the infectee. Under a model with complete transmission bottleneck and no within-host diversity, in which mutations accumulate between the infections of the two cases as a Poisson process of daily rate $LM$ (genome length $L$ times per-site per-day mutation rate $M$), and the time $G$ between the two infections has the generation-time distribution $W$,

$$K \mid G \sim \mathrm{Poisson}(L M G),$$

so $K$ is a mixed Poisson count with

$$\mathbb{E} K = L M\, \mathbb{E} G, \qquad \operatorname{Var} K = L M\, \mathbb{E} G + (L M)^2 \operatorname{Var} G, \qquad \Pr\{K = 0\} = \mathbb{E}\, e^{-L M G}.$$

If $G$ is gamma with mean $m$ and standard deviation $s$, then $\Pr\{K = 0\} = \bigl(1 + L M s^2 / m\bigr)^{-m^2/s^2}$. Models with within-host diversity add the within-host coalescent times to the mixing distribution, which increases and lengthens the tail of $K$.

## Depends on

- [Genetic pseudo-likelihood of a transmission ancestry](genetic-pseudo-likelihood-of-a-transmission-ancestry.md)

## Proof depends on

- [Moment generating function of the gamma distribution](../../../../Probability/distributions/continuous/gamma-distribution/gamma-mgf/mgf-gamma-measure-of-lt.md)

## Expansion

Conditioning on $G$ and using $\mathbb{E}[K \mid G] = \operatorname{Var}[K \mid G] = LMG$ gives the mean and the law of total variance, and $\Pr\{K = 0 \mid G\} = e^{-LMG}$ gives the zero term as the Laplace transform of $G$ at $LM$; the gamma case is the gamma Laplace transform. The quantity $L M\, \mathbb{E} G$ is the expected number of mutations per generation of infection, and when it is well below one most transmission pairs carry identical genomes, so sequences alone cannot order cases. Using literature values for ten pathogens, the mean transmission divergence simulated under the no-diversity model was below one for eight of them, while pathogens such as *K. pneumoniae* and SARS-CoV accumulated enough mutations per generation to discriminate ancestries well. Simulations under a model with within-host diversity gave consistently larger divergences (about 1.6 to 1.8 times on average).

## Sources

- Campbell F, Strang C, Ferguson N, Cori A, Jombart T. When are pathogen genome sequences informative of transmission events? *PLoS Pathogens* (2018), Results, "Transmission divergence", and Materials and methods, "Estimating transmission divergence from simulated outbreaks" and "Outbreak reconstruction", equation (1). DOI <https://doi.org/10.1371/journal.ppat.1006885>. PMCID PMC5821398.
