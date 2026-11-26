# Conditional sojourn-time symmetry of beneficial and deleterious fixations

Consider the diffusion approximation of a diploid, randomly mating Wright–Fisher population of effective size $N_e$, and a new autosomal mutation whose genotypes $AA$, $Aa$, $aa$ have relative fitnesses $1$, $1+hs$, $1+s$ ($|s|\ll1$). Let $t_{s,h}(x)\,dx$ denote the expected time that the mutant allele spends with frequency in $(x,x+dx)$, conditional on its eventual fixation. Then for every $x\in(0,1)$

$$t_{s,h}(x)=t_{-s,\,1-h}(x).$$

In words: conditioned on fixation, a beneficial mutation with selection coefficient $+s$ and dominance $h$ has the same frequency trajectory statistics (sojourn density, hence mean fixation time) as a deleterious mutation with coefficient $-s$ and dominance $1-h$. In particular, a semidominant ($h=\tfrac12$) deleterious mutation that fixes by drift traverses the population as fast as a semidominant beneficial mutation of the same $|s|$, and so produces the same expected hitchhiking footprint on linked neutral sites.

## Proof sketch

Conditioning on fixation is a Doob $h$-transform by the fixation probability $u(x)$: the conditioned diffusion has the same variance $V(x)=x(1-x)/(2N_e)$ and drift $M(x)+V(x)\,u'(x)/u(x)$, where $M(x)=s\,x(1-x)\,[h+(1-2h)x]$. This conditioned drift is invariant under $(s,h)\mapsto(-s,1-h)$, so the two conditioned processes coincide in law and have identical sojourn densities. For $h=\tfrac12$, with $u(x)=(1-e^{-2N_esx})/(1-e^{-2N_es})$, the conditioned drift is $\tfrac{s}{2}\,x(1-x)\coth(N_esx)$, visibly even in $s$. For the neutral case the conditional fixation time has mean $4N_e$ and variance about $4.64N_e^2$, so even neutral fixations can be fast and leave a localised sweep signature. Because deleterious mutations fix appreciably only when $2N_e s\lesssim 1$, the sweeps they cause are weak and narrow.

## Depends on

- [Sojourn density conditioned on fixation](../selection-duality-and-general-one-dimensional-di/conditional-green.md)
- [Drift of an allele under selection with dominance](../selection-duality-and-general-one-dimensional-di/dominance-drift.md)

## Proof depends on

- [Doob h-transform: the Wright–Fisher diffusion conditioned on fixation](../fixation-and-absorption-in-the-wright-fisher-dif/doob-h-transform-process-conditioned-on-fixation.md)

## Sources

- P. Johri, B. Charlesworth, E. K. Howell et al., "Revisiting the notion of deleterious sweeps", Genetics 219(3) (2021) iyab094, Introduction (result of Maruyama and Kimura 1974), <https://doi.org/10.1093/genetics/iyab094>, PMCID PMC9101445.
- T. Maruyama, M. Kimura, "A note on the speed of gene frequency changes in reverse directions in a finite population", Evolution 28 (1974) 161–163, <https://doi.org/10.1111/j.1558-5646.1974.tb00737.x>.
