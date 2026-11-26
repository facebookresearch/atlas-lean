# Strong converse for discrete memoryless channels

Let $W$ be a discrete memoryless channel on finite alphabets, the input alphabet nonempty, with capacity $C$ (in bits). For
every rate $R > C$ and every $\varepsilon < 1$, for all sufficiently large $n$ every code of
blocklength $n$ with $M \ge 2^{nR}$ codewords has average error probability
$\frac1M \sum_m W^{\otimes n}(\{y : g(y) \ne m\} \mid f(m))$ greater than $\varepsilon$. Together
with [achievability](channel-coding-achievability.md), the $\varepsilon$-capacity equals $C$ for
every $0 < \varepsilon < 1$.

Codes here are deterministic and their decoders have no erasure output; the book's converse also
covers randomised codes and erasures, so this statement is weaker than the source's.

## Background

- [Mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md):
  defines the capacity.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 22.1 (`C_ε = C` for `0 < ε < 1`, finite alphabets); J. Wolfowitz (1957).
