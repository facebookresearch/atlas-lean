# Strict improvement over the second binary-code rate bound

For every real $0<\delta<1/2$, the asymptotic binary code rate satisfies $R(\delta)<R_2(\delta)$. Equivalently, for each such $\delta$ there exists $e>0$ with $R(\delta)\le R_2(\delta)-e$. The comparison uses the second, not the first, MRRW objective.

## Depends on

- [Asymptotic binary code rate and the classical first bound](asymptotic-binary-code-rate.md)
- [Second McEliece–Rodemich–Rumsey–Welch rate](second-mrrw-rate.md)

## Proof depends on

- [Binary code rate bounded by the combined variational rate](binary-rate-bounded-by-combined-variational-rate.md)
- [Combined variational rate strictly below the second MRRW rate](combined-variational-rate-strictly-below-second-mrrw.md)

## Proof outline

Combine the combined-variational upper bound with the strict comparison against the second MRRW infimum on the same open interval. Extract a positive margin at each fixed δ.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 2](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `binaryRate_lt_mrrw`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_BinaryCodes.lean#L173-L175)
- [Pinned source: `exists_binaryRate_mrrw_improvement`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_BinaryCodes.lean#L178-L180)
