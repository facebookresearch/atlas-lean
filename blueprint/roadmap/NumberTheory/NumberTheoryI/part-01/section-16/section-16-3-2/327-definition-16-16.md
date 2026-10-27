---
article_id: af_6c79c7a99fd821ac0c4f6b11
declaration: def
origin: cited
statement: formalized
lean: ConvergesLocallyUniformlyOn
---

# Definition 16.16

A sequence of complex functions $(f_n)$ converges uniformly on $S$ if there is a function $f$ such that for every $\epsilon > 0$ there is an integer $N$ for which $\sup_{z \in S} |f_n(z) - f(z)| < \epsilon$ for all $n \geq N$. The sequence $(f_n)$ converges locally uniformly on $S$ if every $z_0 \in S$ has an open neighborhood $U$ for which $(f_n)$ converges uniformly on $U \cap S$. When applied to a series of functions these terms refer to the sequence of partial sums.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 16.3.2](../../../../../../sources/v1/NumberTheoryI.md)
