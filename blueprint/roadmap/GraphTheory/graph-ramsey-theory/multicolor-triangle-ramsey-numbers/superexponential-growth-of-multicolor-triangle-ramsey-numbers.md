# Superexponential growth of multicolor triangle Ramsey numbers

Write $R_k(3)$ for the least size of a complete graph in which every coloring of the edges with $k$ colors has a monochromatic triangle (colors need not all appear). Then $R_k(3)^{1/k}\to+\infty$ as $k\to\infty$ through the natural numbers. The power is in the reals; its value at $k=0$ has no effect. This is the qualitative conclusion of Erdős Problem 183.

## Depends on

- [Multicolor triangle Ramsey number](multicolor-triangle-ramsey-number.md)

## Proof depends on

- [Explicit lower bound for the multicolor triangle Ramsey number](multicolor-triangle-ramsey-number-explic.md)

## Proof outline

Take real kth roots of the explicit lower estimate for k≥2 and show that k^(1/3)/log k tends to infinity; check the eventual positivity needed to take roots.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 9](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Erdős Problem 183](https://www.erdosproblems.com/183)
- [Pinned source: `erdos_183`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/I_MulticolorTriangleRamsey.lean#L18-L22)
