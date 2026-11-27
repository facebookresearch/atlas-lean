# Explicit lower bound for the multicolor triangle Ramsey number

For every
integer $k\ge2$,

$$R_k(3)\ge \left(\frac{k^{1/3}}{6 e^{38}\log k}\right)^k,$$

where $R_k(3)$ is the multicolor triangle Ramsey number, $\log$ is natural,
and the comparison is in $\mathbb R$.

## Depends on

- [Multicolor triangle Ramsey number](multicolor-triangle-ramsey-number.md)

## Proof depends on

- [All-color Ramsey lower bound from palette stages](all-color-ramsey-lower-bound-at-palette-stages.md)

## Proof outline

Handle the bounded range below the first palette threshold separately. For the other color counts use the palette-stage estimate and compare its width with the cube root of the color count to obtain the constant in the displayed bound.

## Sources

- OpenAI, [*Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 9](https://cdn.openai.com/pdf/ten-proofs-oai.pdf), [first clause of the pinned statement](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/I_MulticolorTriangleRamsey.lean#L25-L33).
- [Explicit all-color proof](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2752-L2788)
