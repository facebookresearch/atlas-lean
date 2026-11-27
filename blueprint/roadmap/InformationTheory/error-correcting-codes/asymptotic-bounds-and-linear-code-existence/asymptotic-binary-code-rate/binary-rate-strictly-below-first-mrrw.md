# Strict improvement over the first binary-code rate bound

For every real relative distance $0<\delta<1/2$, the asymptotic binary code rate satisfies $R(\delta)<R_1(\delta)$. Equivalently, for each such $\delta$ there is a real $\varepsilon>0$ with $R(\delta)\le R_1(\delta)-\varepsilon$. The margin may depend on $\delta$.

## Depends on

- [Asymptotic binary code rate and the classical first bound](asymptotic-binary-code-rate.md)

## Expansion

Translate the Hamming spectral certificate to an upper bound on the limsup with natural ceilings. Optimize the feasible pair to make the entropy difference strictly smaller than the classical rate. Any positive margin below the difference gives the existential formulation.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 2](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `binaryRate_lt_classicalRate`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_BinaryCodes.lean#L65-L67)
- [Pinned source: `exists_binaryRate_improvement`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_BinaryCodes.lean#L70-L72)
