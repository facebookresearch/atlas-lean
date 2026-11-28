# Fixation probability and substitution rate of deleterious mutations

In a diploid Wright–Fisher population of $N$ individuals, let a new semidominant mutation (initial frequency $1/(2N)$) have homozygous selection coefficient $s$, $|s|\ll1$. Kimura's diffusion formula gives the fixation probability

$$P_{\mathrm{fix}}(s)=\frac{1-e^{-s}}{1-e^{-2Ns}},$$

so for a deleterious mutation with $s=-s_d$, $s_d>0$,

$$P_{\mathrm{fix}}(-s_d)=\frac{e^{s_d}-1}{e^{2Ns_d}-1}\approx\frac{s_d}{e^{2Ns_d}-1}.$$

If background selection reduces the effective size to $N_e=BN$ with $0<B\le1$, then $P_{\mathrm{fixB}}(-s_d)\approx s_dB/(e^{2NBs_d}-1)$. For a discrete distribution of fitness effects in which a fraction $f_i$ of new mutations falls in class $i$, uniformly on $[s_{d1},s_{d2}]$, the expected number of deleterious fixations per site per generation from class $i$ is

$$N_{\mathrm{fix}}(i)=2N\mu\,f_i\,\frac{1}{s_{d2}-s_{d1}}\int_{s_{d1}}^{s_{d2}}P_{\mathrm{fix}}(-s)\,ds,$$

where $\mu$ is the mutation rate per site per generation, and, treating fixations across $L$ functional sites as a Poisson process, the mean waiting time between deleterious fixations is $t_w=1/(L\,N_{\mathrm{fix}})$.

## Proof sketch

For semidominance the heterozygote has advantage $s/2$, and Kimura's $u(p)=(1-e^{-4N(s/2)p})/(1-e^{-4N(s/2)})$ at $p=1/(2N)$ gives the formula. The factor $e^{2Ns_d}$ makes fixation exponentially unlikely once $2Ns_d\gg1$, so only the weakly deleterious class $0<2Ns_d\le 1$ (and partly $1<2Ns_d\le10$) contributes substitutions. The large mutational input of deleterious mutations relative to beneficial ones can nevertheless make deleterious fixations a non-negligible source of sweep-like signals, especially in between-population statistics such as $F_{ST}$. Background selection enters only through the rescaling $N\mapsto BN$, which raises the fixation probability of weakly deleterious mutations.

## Depends on

- [Kimura's fixation probability](../../kimura-fixation.md)

## Sources

- P. Johri, B. Charlesworth, E. K. Howell et al., "Revisiting the notion of deleterious sweeps", Genetics 219(3) (2021) iyab094, Materials and methods, Equations (1)–(5), <https://doi.org/10.1093/genetics/iyab094>, PMCID PMC9101445.
