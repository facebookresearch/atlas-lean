# Approximate Byzantine agreement: protocols and impossibility

In *approximate agreement*, correct processes start with reals in $[0, 1]$ and must output values within $\varepsilon$ of each other, inside the range of correct inputs. In the synchronous model, iterating the trimmed midpoint for $R$ rounds solves it with $\varepsilon = 2^{-R}$ whenever $n > 3t$. For $2 \le n \le 3t$ no deterministic synchronous protocol achieves $\varepsilon$-agreement with $\varepsilon < 1$ on inputs in $[0, 1]$ in any fixed number of rounds.

## Proof sketch

Each round halves the range of correct values by the contraction lemma while preserving validity. The impossibility uses the same partition and covering argument as the $3t$ node bound for exact agreement.

## Depends on

- [Validity and contraction of the trimmed midpoint](validity-and-contraction-of-the-trimmed-midpoint.md)
- [Reaching Byzantine agreement](../../byzantine-agreement/solves.md)

## Proof depends on

- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../../byzantine-agreement/not-solves-of-card-le-three-mul.md)

## Sources

- Danny Dolev et al., "Reaching Approximate Agreement in the Presence of Faults", Journal of the ACM, 1986.
