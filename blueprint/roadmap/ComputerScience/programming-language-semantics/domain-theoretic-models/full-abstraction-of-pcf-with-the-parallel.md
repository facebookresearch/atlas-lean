# Full abstraction of PCF with the parallel conditional

For terms $M$ and $N$ of the same type of [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md), the standard model is fully abstract:

1. $M \sqsubseteq_{PA} N$ if and only if $\mathcal{A}_{PA}[\![M]\!] \sqsubseteq \mathcal{A}_{PA}[\![N]\!]$ (in every environment);
2. $M \simeq_{PA} N$ if and only if $\mathcal{A}_{PA}[\![M]\!] = \mathcal{A}_{PA}[\![N]\!]$.

The direction from denotations to behaviour is computational adequacy. For the converse, if the denotations of closed $M$ and $N$ differ, they differ
on finite arguments, since the domains are algebraic; these arguments are definable, and applying $M$ and $N$ to their definitions gives programs
with different results. Without the parallel conditional the same model is [not fully abstract](the-scott-model-of-pcf-is-not-fully-abstract.md).

## Depends on

- [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md)

## Proof depends on

- [Finite elements are definable in PCF with the parallel conditional](finite-elements-are-definable-with-parallel.md)
- [Computational adequacy for PCF](../pcf-and-computational-adequacy/adequacy.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 4, Theorem 4.3 and its proof on pages 238–239, with Theorem 4.1 and the analogue of Theorem 3.1 for $\mathcal{L}_{PA}$.
