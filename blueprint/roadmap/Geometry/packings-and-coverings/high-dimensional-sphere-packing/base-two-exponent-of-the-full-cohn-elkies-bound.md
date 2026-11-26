# Logarithmic exponents of the full Cohn–Elkies bound

As $d\to\infty$ through the natural numbers,

$$\frac{\log B_d}{d}\longrightarrow \tfrac12\log(e/(2\pi)),\qquad
\frac{\log_2 B_d}{d}\longrightarrow -c_2,
\quad c_2=\tfrac12\log_2(2\pi/e).$$

In particular there is a real sequence $e_d\to0$ such that eventually $B_d=2^{-(c_2+e_d)d}$.

## Depends on

- [Full Cohn–Elkies linear-programming bound](full-cohn-elkies-linear-program.md)

## Proof depends on

- [Root limit of the full Cohn–Elkies bound](root-limit-of-the-full-cohn-elkies-bound.md)

## Proof outline

Establish eventual positivity of B_d and use continuity of log at the positive root limit. Normalize the logarithmic difference to recover the vanishing-error expression.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 1](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `exact_binary_exponent`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/A_SpherePacking.lean#L153-L159)
- [Pinned source: `sharpFullCohnElkiesManuscriptConclusions`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/A_SpherePacking.lean#L179-L180)
