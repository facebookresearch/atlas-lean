# Normal-form LWE: secrets drawn from the error distribution

Let $q$ be a positive integer and $\chi$ an error distribution on $\mathbb{Z}_q$. In *normal-form* LWE the secret $s$ is drawn from $\chi^n$ instead of uniformly. There is an efficient transformation $T$ from $n + m$ standard LWE samples to $m$ normal-form samples: write the sample as $(A, b)$ with $A = \binom{A_1}{A_2}$, $A_1 \in \mathbb{Z}_q^{n \times n}$; if $A_1$ is invertible, output $(A', b')$ with $A' = -A_2 A_1^{-1}$ and $b' = b_2 + A' b_1$. If $b = A s + e$ then $b' = A' e_1 + e_2$, an LWE sample with secret $e_1 \sim \chi^n$, and $A'$ is uniform given that $A_1$ is invertible; if $b$ is uniform then so is $b'$. Consequently, for every adversary $D$ against normal-form decision (respectively search) LWE with $m$ samples there is an adversary against standard decision (respectively search) LWE with $n + m$ samples, running $T$ and then $D$, whose advantage (success probability) is at least that of $D$ minus $\Pr[A_1 \text{ singular}]$ for uniform $A_1 \in \mathbb{Z}_q^{n\times n}$.

## Proof sketch

Conditioned on $A_1$ invertible, $(A_1, A')$ is uniform on invertible matrices times all matrices, so the transformed pair has exactly the normal-form law in the real case and the uniform law in the random case. The two cases differ from the conditional ones by at most the singularity probability.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)

## Proof depends on

- [LWE with uniform errors has zero advantage](lwe-with-uniform-error.md)

## Sources

- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
