# Observational equivalence is labelled bisimilarity

**Theorem (Abadi and Fournet).** On closed extended processes of the applied pi calculus,
[observational equivalence](observational-equivalence-in-the-applied-pi-calculus.md) coincides with
[labelled bisimilarity](labelled-bisimilarity-in-the-applied-pi-calculus.md): $\approx\ =\ \approx_l$.

In particular $\approx_l$ is closed under closing evaluation contexts, so labelled bisimulations, which quantify over no contexts, prove observational equivalence.

## Depends on

- [Observational equivalence in the applied pi calculus](observational-equivalence-in-the-applied-pi-calculus.md)
- [Labelled bisimilarity in the applied pi calculus](labelled-bisimilarity-in-the-applied-pi-calculus.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 4.3, Theorem 4.1, with its proof outlined in Section 4.5 and completed in the appendix.
- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 5.3.3, Theorem 5.1.
