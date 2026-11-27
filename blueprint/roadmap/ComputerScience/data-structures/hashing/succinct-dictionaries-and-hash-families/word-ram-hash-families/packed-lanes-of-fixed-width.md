# Packed lanes of fixed width in a word

A word holds $m$ *packed lanes* of width $W$ if lane $j$ occupies bits $[jW, (j+1)W)$, with $mW \le w$. Lane read is $\mathrm{lane}_j(x) = \lfloor x / 2^{jW} \rfloor \bmod 2^W$, lane write replaces those bits, and two words agree iff all their lanes agree when both are below $2^{mW}$. Multiplying a value $v < 2^W$ by $\sum_{j<m} 2^{jW}$ replicates it into every lane. These primitives underlie word-parallel comparison and rank.

## Depends on

- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
