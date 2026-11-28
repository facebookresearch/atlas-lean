# Fixation probability under serial dilution

Consider the [serial-dilution model](selection-coefficient-under-serial-dilution.md): a batch culture with resource $R$ grows to saturation, is diluted by the factor $D > 1$ by keeping each cell independently with probability $1/D$, and new mutations arise at cell divisions during exponential growth. A beneficial mutant with relative growth rate $\gamma$ and relative lag $\omega$ against the background on which it arose has selection coefficient $s = \gamma \ln D - \omega$.

**Strong-selection weak-mutation regime.** When mutations arise and fix or are lost one at a time (small bottleneck $N_0 \approx R/D$), the fixation probability of a single new beneficial mutant with $0 < s \ll 1$ is

$$\varphi_{\mathrm{SSWM}}(s) = \frac{2 \ln D}{D - 1}\, s.$$

**Clonal interference.** For larger populations the fixation probability is well described by the empirical form

$$\varphi_{\mathrm{CI}}(s) = A\, s\, e^{-B/s},$$

with constants $A, B > 0$ that depend on $D$, $R$ and the distribution of mutational effects; the Gerrish–Lenski argument predicts $A = 2 \ln D / (D - 1)$.

In both regimes the fixation probability depends on the growth traits only through $s$: mutants with different combinations of $(\gamma, \omega)$ but the same $s$ fix with the same probability, even though selection in the full model is frequency dependent and has higher-order interactions.

## Proof sketch

The prefactor differs from Haldane's $2s$ because a mutation arising during exponential growth can appear at any point of the cycle. A mutant cell born when the population is a fraction of its final size reaches the bottleneck as a clone whose size depends on its birth time; averaging the branching-process survival probability over birth times weighted by the number of divisions at each time gives the factor $\ln D/(D - 1)$ relative to a mutant present at the start of the cycle. Under clonal interference, $e^{-B/s}$ is the probability that no superior mutation arises before the focal mutation fixes: the fixation time scales as $1/s$, so the expected number of competing superior mutations is proportional to $1/s$. The form fails for weak mutations that fix only by hitchhiking. In simulations the SSWM formula matches $N_0 \approx 10^3$ and the clonal-interference form matches $N_0 \gtrsim 10^4$.

## Depends on

- [Selection coefficient of growth traits under serial dilution](selection-coefficient-under-serial-dilution.md)

## Proof depends on

- [Haldane's approximation $\pi(s) \approx 2s$](../../../haldane-s-survival-probability-of-a-beneficial-m/tendsto-survival-prob-div.md)

## Sources

- J. Lin, M. Manhart and A. Amir, "Evolution of microbial growth traits under serial dilution", Genetics (2020), <https://doi.org/10.1534/genetics.120.303149>, PMCID PMC7337084. Section on fixation of new mutations, Equations 5 and 6 and Figure 2.
- P. J. Gerrish and R. E. Lenski, "The fate of competing beneficial mutations in an asexual population", Genetica 102/103 (1998), 127–144, <https://doi.org/10.1023/A:1017067816551>.
