# Strict decrease of spherical code hierarchy levels

For every $0<s<1$ and every natural $r$,

$$L_{r+1}(s)<L_r(s),\qquad L_{r+1}^{\rm loc}(s)<L_r^{\rm loc}(s).$$

Both assertions compare consecutive levels, including the first step from level zero.

## Depends on

- [Interlaced variational objectives for spherical codes](interlaced-spherical-code-objectives.md)
- [Sidelnikov localization of spherical code bounds](sidelnikov-localized-rates.md)

## Expansion

Construct a strictly improving extra interlacing pair and prove strictness persists after localization; pointwise monotonicity alone does not prove a strict inequality of infima.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 2](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `strict_hierarchy`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/B_SphericalCodes.lean#L275-L283)
