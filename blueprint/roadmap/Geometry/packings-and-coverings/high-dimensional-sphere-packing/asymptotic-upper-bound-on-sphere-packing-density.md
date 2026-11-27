# Sphere packing density upper bound from the full program

There is a real sequence $e_d=o(1)$ for which, for **every** positive integer $d$,

$$\Delta_d\le \max\bigl(0,(\sqrt{e/(2\pi)}+e_d)^d\bigr),$$

where the right side is viewed in the extended nonnegative reals. The error can absorb finitely many small dimensions. This is an upper bound for the packing density, not a claim that the packing density attains the program asymptotic.

## Depends on

- [Upper density of a Euclidean sphere packing](upper-density-of-a-sphere-packing.md)

## Proof depends on

- [Full Cohn–Elkies linear-programming bound](full-cohn-elkies-linear-program.md)
- [Root limit of the full Cohn–Elkies bound](root-limit-of-the-full-cohn-elkies-bound.md)

## Expansion

Prove the packing-to-program bound in the same separation and volume convention, apply the program asymptotic, and justify a finite adjustment of the error sequence for every positive dimension.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 1](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `sphere_packing_sharp_asymptotic_upper`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/A_SpherePacking.lean#L166-L172)
