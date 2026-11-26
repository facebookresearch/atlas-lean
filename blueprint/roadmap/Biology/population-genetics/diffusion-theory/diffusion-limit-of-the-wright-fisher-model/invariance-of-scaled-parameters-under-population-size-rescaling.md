# Invariance of scaled parameters under population-size rescaling

Consider a diploid Wright–Fisher population of $N$ individuals ($2N$ gene copies) with per-generation mutation rate $\mu$, genic selection coefficient $s$ and recombination fraction $r$ between two loci. Its diffusion approximation runs in time $\tau = t/(2N)$ (with $t$ in generations) and depends on the model only through the scaled parameters

$$\theta = 4N\mu, \qquad \sigma = 2Ns, \qquad \rho = 4Nr.$$

Fix a rescaling factor $Q > 1$ such that $Q\mu$, $Q|s|$ and $Qr$ remain admissible per-generation rates (in particular $Qr \le 1/2$), and define the **rescaled model** $N' = N/Q$, $\mu' = Q\mu$, $s' = Qs$, $r' = Qr$, with every demographic epoch length and the run time divided by $Q$.

**Proposition.**

1. $(\theta, \sigma, \rho)$ are unchanged, and $\tau' = t'/(2N') = t/(2N) = \tau$ when $t' = t/Q$; hence every quantity of the diffusion limit expressed in $(\theta,\sigma,\rho,\tau)$ and in allele frequencies is identical for the original and rescaled models. Examples are [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation-two-mul-mul.md) $u(p) = (1 - e^{-4Nsp})/(1 - e^{-4Ns})$ at a fixed initial frequency $p$, and the Sawyer–Hartl frequency spectrum.
2. Quantities measured in generations scale by $1/Q$: the neutral expected pairwise coalescence time $2N$ becomes $2N/Q$, so event times of the rescaled run must be multiplied by $Q$.
3. The single-copy initial frequency is not invariant: $p' = 1/(2N') = Qp$. The fixation probability of one new mutant becomes $(1 - e^{-2Qs})/(1 - e^{-4Ns})$ instead of $(1 - e^{-2s})/(1 - e^{-4Ns})$ in the diffusion formula, so the substitution rate per original generation, $Q^{-1} \cdot 2N'\mu' \cdot u'(p')$, equals the original rate times $\dfrac{1 - e^{-2Qs}}{Q\,(1 - e^{-2s})}$, which tends to $1$ only when $Qs \to 0$.

The finite-population chain itself is not invariant under rescaling: the error of the diffusion approximation grows as $N'$ shrinks and as $Q|s|$, $Q\mu$, $Qr$ grow, and these errors are the source of the biases that Dabi and Schrider (2024) measure in fixation times, allele-frequency spectra, linkage disequilibrium and fixed fractions of mutations, even at small $Q$.

## Depends on

- [Wright–Fisher diffusion limit, generator form](tendsto-wf-generator.md)
- [Kimura's fixation probability in terms of 4Ns, for nonzero Ns](../wright-fisher-diffusion/kimura-fixation-two-mul-mul.md)

## Expansion

Items 1 and 2 are substitutions: $4(N/Q)(Q\mu) = 4N\mu$, $2(N/Q)(Qs) = 2Ns$, $4(N/Q)(Qr) = 4Nr$ and $(t/Q)/(2N/Q) = t/(2N)$; the limiting generator and its boundary behaviour depend only on these. For item 3, $4N's'p' = 4Ns \cdot Q/(2N) = 2Qs$, and the factor $Q^{-1}$ converts a per-generation rate of the compressed run into a rate per original generation. Expanding $1 - e^{-2Qs} = 2Qs - 2Q^2s^2 + O(Q^3 s^3)$ shows the relative error is of order $Qs$ for small $Qs$. Positive results on the finite chain need a quantitative bound on the diffusion error, which rescaling makes larger; this is why rescaling is a heuristic rather than an exact symmetry.

## Sources

- A. Dabi and D. R. Schrider, "Population size rescaling significantly biases outcomes of forward-in-time population genetic simulations", Genetics 229(1) (2025), iyae180, <https://doi.org/10.1093/genetics/iyae180>, PMCID PMC11708920 (Introduction: $\theta_{\mathrm{scaled}} = 4(N/Q)(Q\mu) = 4N\mu$, the $2N/Q$ coalescence timescale, and the simulation study of rescaling biases). Item 3 is derived above.
