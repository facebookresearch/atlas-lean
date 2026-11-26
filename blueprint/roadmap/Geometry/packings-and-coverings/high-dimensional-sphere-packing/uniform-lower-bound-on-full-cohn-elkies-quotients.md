# Uniform lower bound on admissible Cohn–Elkies quotients

There exists one sequence $\delta_d\ge0$ for every $d\in\mathbb N$, tending to zero, such that in every sufficiently large $d$ and for every admissible $f$ in that dimension,

$$Q(f)\ge \frac{2^d}{V_d}(\sqrt{e/(2\pi)}-\delta_d)^d.$$

The cutoff and the error sequence are independent of the test function.

## Depends on

- [Full Cohn–Elkies linear-programming bound](full-cohn-elkies-linear-program.md)

## Proof depends on

- [Root limit of the full Cohn–Elkies bound](root-limit-of-the-full-cohn-elkies-bound.md)

## Proof outline

Pass from the rooted-program limit to an eventual lower error envelope independent of f and use that the infimum of quotients is a lower bound for every quotient.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 1](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `sharpFullCohnElkiesManuscriptConclusions`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/A_SpherePacking.lean#L179-L180)
