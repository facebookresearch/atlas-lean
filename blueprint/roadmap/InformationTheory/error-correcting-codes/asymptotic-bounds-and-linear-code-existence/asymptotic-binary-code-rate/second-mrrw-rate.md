# Second McEliece–Rodemich–Rumsey–Welch rate

For $0<\delta<1/2$ and $g(v)=h((1-\sqrt{1-v})/2)$, set

$$R_2(\delta)=\inf_{0\le r\le1-2\delta}\big[1+g(r^2)-g(r^2+2\delta r+2\delta)\big].$$

The endpoints in the infimum are included. This is a different comparison objective from $R_1$.

## Depends on

- [Asymptotic binary code rate and the classical first bound](asymptotic-binary-code-rate.md)

## Implementation notes

Check the domain of the square root and the entropy arguments over the closed feasible interval; use continuous real optimization on that interval.

## Sources

- [Pinned second comparison rate](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_BinaryCodes.lean#L154-L166)
