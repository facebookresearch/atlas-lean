# Mutation burden, the burden ratio and the additive response to a bottleneck

**Model.** Deleterious derived alleles arise at rate $U_d$ per haploid genome per generation (one-way mutation, infinite sites, free recombination) in a diploid population of $N$ individuals. At each site the genotype fitnesses are $1$, $1-hs$, $1-s$ for $0$, $1$, $2$ derived copies, with $s>0$ and dominance coefficient $h \ge 0$ ($h = 1/2$ additive, $h = 0$ recessive). In the approximate mutation–selection–drift equilibrium (rare fixations, no back mutation), the density of polymorphic derived alleles at frequency $x \in (0,1)$ is Kimura's

$$\phi_{\mathrm{eq}}(x) = \frac{4NU_d\, e^{-4Nshx-2Ns(1-2h)x^2}}{x(1-x)}\left[1-\frac{\int_0^x e^{4Nshy+2Ns(1-2h)y^2}\,dy}{\int_0^1 e^{4Nshy+2Ns(1-2h)y^2}\,dy}\right].$$

For $h=1/2$ this is $\theta\,\bigl(1-e^{2Ns(1-x)}\bigr)/\bigl(x(1-x)(1-e^{2Ns})\bigr)$ with $\theta = 4NU_d$.

**Definitions.** The *mutation burden* is the expected number of derived deleterious alleles per haploid genome, the first moment of the spectrum,

$$\langle x\rangle = \int_0^1 x\,\phi(x)\,dx .$$

Compare an *equilibrium* population of constant size $N_0$ with a *founded* population that split from it, stayed at size $N_B$ for $T_B$ generations, and then re-expanded to $N_0$; time $t$ counts generations since re-expansion and $I_B = T_B/(2N_B)$ is the bottleneck intensity. The *burden ratio* is

$$B_R(t) = \frac{\langle x\rangle_{\mathrm{eq}}}{\langle x\rangle_{\mathrm{founded}}(t)}.$$

Since both burdens are proportional to $U_d$, the ratio does not depend on the mutation rate.

**Additive selection ($h = 1/2$).** Summing the forward equation over sites gives the first-moment equation

$$\partial_t \langle x\rangle \approx U_d - \frac{s}{2}\bigl(\langle x\rangle - \langle x^2\rangle\bigr),$$

in which genetic drift does not appear directly. When $2N_0 s \gg 1$ and $\langle x^2\rangle \ll \langle x\rangle$ this is solved by the deterministic balance $\langle x\rangle \approx 2U_d/s$. Then:

- if selection stays efficient during the bottleneck ($2N_B s \gg 1$), $\langle x\rangle_{\mathrm{founded}} \approx 2U_d/s$ throughout and $B_R \approx 1$;
- if selection is fully relaxed during the bottleneck ($2N_B s \ll 1$) and $I_B \ll 1$, about $U_d T_B$ new mutations accumulate and are purged after re-expansion:

$$\langle x(t)\rangle_{\mathrm{founded}} \approx \frac{2U_d}{s} + U_d T_B\, e^{-st/2}, \qquad B_R(t) \approx \Bigl(1+\tfrac{sT_B}{2}\,e^{-st/2}\Bigr)^{-1} \le 1 .$$

So for additive alleles a bottleneck never lowers the burden: $B_R \le 1$, and the excess decays on the time scale $2/s$.

## Depends on

- [Drift of an allele under selection with dominance](../../diffusion-theory/selection-duality-and-general-one-dimensional-di/dominance-drift.md)
- [Sawyer–Hartl Poisson random field density](../../diffusion-theory/poisson-random-field-model/prf-density.md)
- [Mutation–selection balance in a haploid population](../haploid-mutation-selection-balance.md)

## Expansion

The first-moment equation follows by multiplying the diffusion forward equation by $x$ and integrating: the drift term integrates to zero (drift does not change the expected frequency), mutation contributes the influx $U_d$ of new alleles at frequency $1/(2N)$ per copy, and additive selection contributes $-\tfrac{s}{2}x(1-x)$ per site. With $\langle x^2\rangle$ negligible the equation is linear, with equilibrium $2U_d/s$ and relaxation rate $s/2$. A bottleneck with relaxed selection adds $U_d T_B$ to the burden while leaving $\langle x^2\rangle$ small when $I_B \ll 1$, and the linear equation then removes this excess exponentially.

## Sources

- D. J. Balick, R. Do, C. A. Cassa, D. Reich and S. R. Sunyaev, "Dominance of deleterious alleles controls the response to a population bottleneck", PLoS Genetics (2015), Results, Eqs. (1)–(10), <https://doi.org/10.1371/journal.pgen.1005436>, PMCID PMC4552954.
