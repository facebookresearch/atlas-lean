# Randomly fluctuating selection

Biswas, Etheridge and Klimek (2021, Section 1, equation (1.1)) consider two alleles in an environment that switches between two states, each favouring one allele, with selection strong enough that either allele would fix quickly in a constant environment but balanced between the two states, and fluctuations fast on evolutionary time scales. Over large time scales the frequency $p$ of one allele follows

$$dp = s^2p(1 - p)(1 - 2p)\,dt + \sqrt{p(1 - p)}\,dB^1 + \sqrt2\,sp(1 - p)\,dB^2,$$

with independent Brownian motions $B^1$ for genetic drift and $B^2$ for the environmental fluctuations and a scaled selection coefficient $s$; they recover this equation as a scaling limit of a Lambda–Fleming–Viot model (their Section 3), and it coincides with the limit that Gillespie (2004) obtained from a Wright–Fisher type model. The generator is therefore $\frac12[p(1 - p) + 2s^2p^2(1 - p)^2]\partial_p^2 + s^2p(1 - p)(1 - 2p)\partial_p$: the environmental noise adds the variance $2s^2p^2(1 - p)^2$, of order $p^2$ near $0$ rather than $p$, and a drift. The drift equals the Itô–Stratonovich correction of the environmental noise term: for the noise coefficient $g(p) = \sqrt2\,sp(1 - p)$, $\frac12g(p)g'(p) = s^2p(1 - p)(1 - 2p)$ (Øksendal 2003, Section 3.3, Itô–Stratonovich conversion), so the environmental part of the limit is the Stratonovich equation $\sqrt2\,sp(1 - p)\circ dB^2$ with no mean selection. The form of the drift is thus fixed by the explicit environmental process and scaling, not by inserting a Gaussian selection term by analogy.

## Expansion

1. The two-environment model with balanced strong selection and fast switching, and its scaling regime.
2. The limiting equation with drift and environmental noise, and its generator.
3. The identification of the drift with the Itô–Stratonovich correction of the environmental noise.
4. Boundary behaviour under fluctuating selection: the environmental variance vanishes to second order at $0$ and $1$.
5. The spatial version, a stochastic partial differential equation in one dimension, and the higher-dimensional limits.

## Sources

- N. Biswas, A. M. Etheridge and A. Klimek, The spatial Lambda-Fleming-Viot process with fluctuating selection, Electron. J. Probab. 26 (2021), 1–51; Sections 1 and 3 and equation (1.1) in the numbering of the arXiv version, arXiv:1802.08188v2. <https://doi.org/10.1214/21-EJP593>
- B. Øksendal, *Stochastic Differential Equations: An Introduction with Applications*, 6th ed., Springer, 2003, Section 3.3, comparison of Itô and Stratonovich integrals.
