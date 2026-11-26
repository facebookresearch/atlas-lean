# Theta growth of the logarithmic multicolor triangle Ramsey number

As $k\to\infty$ through the natural numbers, $\log R_k(3)=\Theta(k\log k)$. Thus some constants $c,C>0$ satisfy $c k\log k\le \log R_k(3)\le C k\log k$ for every sufficiently large $k$; all logarithms are natural.

## Depends on

- [Multicolor triangle Ramsey number](multicolor-triangle-ramsey-number.md)

## Proof depends on

- [Logarithmic coefficients for multicolor triangle Ramsey numbers](logarithmic-coefficients-for-multicolor-triangle-ramsey-numbers.md)

## Proof outline

Specialize the two coefficient inequalities to any fixed ε strictly between 0 and 1/3. Use eventual positivity of k log k to convert them to both real big-O directions.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 9](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `triangleRamseyNumber_log_isTheta`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/I_MulticolorTriangleRamsey.lean#L45-L47)
