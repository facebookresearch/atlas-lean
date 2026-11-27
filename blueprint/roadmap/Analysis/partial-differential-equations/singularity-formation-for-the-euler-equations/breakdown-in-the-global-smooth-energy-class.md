# Breakdown in the global smooth Euler energy class

There exists a smooth divergence-free $u_0$ on $\mathbb R^3$ with rapid initial decay for which no global smooth unforced Euler velocity–pressure pair exists in the whole-space energy class. The formal breakdown conclusion alone does not quantify a lifespan and does not require compact support in its statement.

## Depends on

- [Whole-space smooth Euler energy class](whole-space-smooth-euler-energy-class.md)

## Proof depends on

- [Compact smooth Euler data with a finite singular lifespan](compact-smooth-euler-singularity.md)

## Proof outline

Use the global-obstruction clause of the compact smooth singularity theorem, discarding compact support, nonzero datum and lifespan witnesses. Do not substitute maximality in the all-orders Sobolev class for nonexistence in the smooth energy class.

## Sources

- [OpenAI, *Finite time blowup for the Euler equation*, Theorem 1.1](https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf)
- [Pinned source: `euler_breakdown_R3`](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/Euler.lean#L85-L87)
