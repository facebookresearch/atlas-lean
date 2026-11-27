# Weak converse for discrete memoryless channels

Let $W$ be a discrete memoryless channel on finite alphabets, the input alphabet nonempty, with capacity $C$ (in bits). Every
code of blocklength $n$ with $M \ge 1$ codewords and average error probability $P_e$ satisfies

$$
(1 - P_e) \log_2 M \le n C + h(P_e),
$$

where $h$ is the binary entropy in bits. The proof combines Fano's inequality with the
data-processing inequality and the tensorization $\max I(X^n; Y^n) = nC$.

Codes here are deterministic and their decoders have no erasure output; the book's converse also
covers randomised codes and erasures, so this statement is weaker than the source's.

## Informally uses

- [Fano's inequality](../../information-inequalities/fano-s-inequality/fano-inequality.md):
  bounds the equivocation of the message by the error probability. The linked statement assumes all
  joint probabilities positive; the converse uses its extension to nonnegative laws by continuity, and
  the case $M = 1$ is immediate.
- [Data-processing inequality for mutual information](../../information-inequalities/data-processing-inequality/measure-mutual-information-comp-le.md):
  $I(W; \hat W) \le I(X^n; Y^n)$.

## Background

- [Mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md):
  defines the capacity.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 17.3 (`log M ≤ (sup I(X; Y) + h(ε)) / (1 - ε)`) applied to the `n`-letter channel, with Proposition 19.10 (`sup I(Xⁿ; Yⁿ) = n C`), as in Theorem 19.7.
