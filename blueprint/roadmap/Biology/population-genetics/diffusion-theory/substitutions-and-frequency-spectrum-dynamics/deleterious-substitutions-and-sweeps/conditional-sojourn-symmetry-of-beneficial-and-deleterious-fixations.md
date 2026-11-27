# Conditional sojourn-time symmetry of beneficial and deleterious fixations

Consider the diffusion approximation of a diploid, randomly mating Wright–Fisher population of effective size $N_e$, and a new autosomal **semidominant** mutation whose genotypes $AA$, $Aa$, $aa$ have relative fitnesses $1$, $1+s/2$, $1+s$ ($|s|\ll1$, dominance $h = \tfrac12$). Let $t_{s}(x)\,dx$ denote the expected time that the mutant allele, started from a single copy, spends with frequency in $(x,x+dx)$, conditional on its eventual fixation. Then for every $x\in(0,1)$

$$t_{s}(x)=t_{-s}(x).$$

In words: conditioned on fixation, a semidominant beneficial mutation with selection coefficient $+s$ has the same frequency trajectory statistics (sojourn density, hence mean fixation time) as a semidominant deleterious mutation with coefficient $-s$. In particular, a semidominant deleterious mutation that fixes by drift traverses the population as fast as a semidominant beneficial mutation of the same $|s|$, and so produces the same expected hitchhiking footprint on linked neutral sites.

**No same-frequency identity for general dominance.** For $h \ne \tfrac12$ the analogous identity $t_{s,h}(x) = t_{-s,1-h}(x)$ fails. With $M(x)=s\,x(1-x)\,[h+(1-2h)x]$, $V(x) = x(1-x)/(2N_e)$, scale density $S'(y)=\exp(-4N_es[hy+(1-2h)y^2/2])$ and $S(x) = \int_0^x S'$, the conditional sojourn density of a new copy started below $x$ is $2S(x)(S(1)-S(x))/(S(1)V(x)S'(x))$. At $N_e = 100$ and $x = \tfrac14$ it is about $347.37$ generations per unit frequency for $(s,h) = (0.01, 0)$ but about $329.34$ for $(s,h) = (-0.01, 1)$, while both semidominant values $(\pm 0.01, \tfrac12)$ equal about $377.09$. Exchanging $(s,h) \mapsto (-s, 1-h)$ amounts to relabelling the alleles, which reflects frequency $x \mapsto 1 - x$ and reverses which allele is conditioned to fix; it does not compare the two densities at the same $x$.

## Proof sketch

Conditioning on fixation is a Doob $h$-transform by the fixation probability $u(x)$: the conditioned diffusion has the same variance $V(x)$ and drift $M(x)+V(x)\,u'(x)/u(x)$. For $h=\tfrac12$, $M(x) = \tfrac{s}{2}x(1-x)$ and $u(x)=(1-e^{-2N_esx})/(1-e^{-2N_es})$, so the conditioned drift is $\tfrac{s}{2}\,x(1-x)\coth(N_esx)$, which is even in $s$. The two conditioned processes therefore coincide in law and have identical sojourn densities. For the neutral case the conditional fixation time has mean $4N_e$ and variance about $4.64N_e^2$, so even neutral fixations can be fast and leave a localised sweep signature. Because deleterious mutations fix appreciably only when $2N_e |s|\lesssim 1$, the sweeps they cause are weak and narrow.

## Depends on

- [Sojourn density conditioned on fixation](../../selection-duality-and-general-one-dimensional-di/conditional-green.md)
- [Drift of an allele under selection with dominance](../../selection-duality-and-general-one-dimensional-di/dominance-drift.md)

## Proof depends on

- [Doob h-transform: the Wright–Fisher diffusion conditioned on fixation](../../fixation-and-absorption-in-the-wright-fisher-dif/doob-h-transform-process-conditioned-on-fixation.md)

## Sources

- P. Johri, B. Charlesworth, E. K. Howell et al., "Revisiting the notion of deleterious sweeps", Genetics 219(3) (2021) iyab094, Introduction (result of Maruyama and Kimura 1974) and Methods (simulations of semidominant mutations, $h = 0.5$), <https://doi.org/10.1093/genetics/iyab094>, PMCID PMC9101445.
- T. Maruyama, M. Kimura, "A note on the speed of gene frequency changes in reverse directions in a finite population", Evolution 28 (1974) 161–163, <https://doi.org/10.1111/j.1558-5646.1974.tb00736.x>.
