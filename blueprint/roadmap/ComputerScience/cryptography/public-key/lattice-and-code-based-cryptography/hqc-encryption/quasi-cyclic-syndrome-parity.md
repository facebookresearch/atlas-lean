# Parity constraint of quasi-cyclic syndromes

In $\mathcal{R} = \mathbb{F}_2[X]/(X^n - 1)$, the parity (sum of coordinates) is a ring homomorphism to $\mathbb{F}_2$, so for every $h$ and fixed-weight $x, y$ the syndrome $s = x + h y$ has parity $|x| + |h|\,|y| \bmod 2$. Hence the real quasi-cyclic syndrome distributions with fixed secret weights are supported on vectors of a determined parity, and the decisional quasi-cyclic syndrome decoding problems compare them with the uniform distribution on vectors of that parity rather than on all of $\mathbb{F}_2^n$.

## Proof sketch

Evaluating at $X = 1$ is a ring homomorphism $\mathcal{R} \to \mathbb{F}_2$ that maps a vector to its parity.

## Depends on

- [HQC public-key encryption](hqc-public-key-encryption.md)

## Sources

- Philippe Gaborit et al., "Hamming Quasi-Cyclic (HQC)", Version 5.1, November 9, 2026.
