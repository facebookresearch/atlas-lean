# Full Cohn–Elkies linear-programming bound

In dimension $d$, call a complex Schwartz function $f$ on $\mathbb R^d$ admissible if $f$ and its Euclidean Fourier transform $\hat f$ are real-valued, $\hat f\ge0$ everywhere, $\hat f(0)>0$, and $f(x)\le0$ for $\|x\|\ge1$. Take the Fourier convention with kernel $e^{-2\pi i x\cdot\xi}$ and Lebesgue measure. Set $Q(f)=f(0)/\hat f(0)$ and $V_d=\pi^{d/2}/\Gamma(d/2+1)$. The full bound is

$$B_d=V_d 2^{-d}\inf_{f\text{ admissible}}Q(f).$$

There is no restriction to an ansatz or a fixed-degree radial family. Real roots in the formulas below are real powers, and the root-before-infimum construction takes the infimum of the rooted quotients, not a minimum over extremizers.

## Implementation notes

Reuse the Schwartz Fourier transform, check normalization and the radius-one exterior condition, and prove nonemptiness, boundedness and positivity facts for the quotient infimum. Do not substitute the separate dimension-four density bound for this full optimization.

## Sources

- [Pinned admissibility, quotient and program](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/A_SpherePacking.lean#L12-L54)
