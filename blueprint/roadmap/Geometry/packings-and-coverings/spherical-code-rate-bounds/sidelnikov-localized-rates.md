# Sidelnikov localization of spherical code bounds

For a real rate function $L$, its localization is

$$\mathcal T L(s)=\inf_{0\le t\le s}\left[L(t)+\tfrac12\log_2\frac{1-t}{1-s}\right].$$

Write $L_r^{\rm loc}=\mathcal T L_r$ and $L_*^{\rm loc}(s)=\inf_{r\ge0}L_r^{\rm loc}(s)$. The localized row rate $L_{\rm row}^{\rm loc}$ applies $\mathcal T$ to the infimum of $h_S(a)-h_S(b)$ over $0<b<a$ with

$$t<\frac{2(a-b)(1+a+b)}{(1+2a)\sqrt{a(1+a)}}.$$

The classical localized rate $L_{\rm clsl}^{\rm loc}$ applies $\mathcal T$ to $t\mapsto h_S((1/\sqrt{1-t^2}-1)/2)$. Both endpoints of the localization interval are included.

## Depends on

- [Interlaced variational objectives for spherical codes](interlaced-spherical-code-objectives.md)

## Implementation notes

Prove the underlying objective bounds and handle t=0 in the entropy, spectral feasibility, and logarithm conventions. Then formalize the localization inequality and compare exact meanings of the row, level-zero and classical objectives.

## Sources

- [Pinned single-row and localization definitions](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L28-L36)
- [Pinned localization cost and envelope](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L169-L186)
- [Pinned localized rates](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L252-L264)
