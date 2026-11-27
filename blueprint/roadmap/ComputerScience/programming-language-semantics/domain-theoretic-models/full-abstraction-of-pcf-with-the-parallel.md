# Full abstraction of PCF with the parallel conditional

For terms $M$ and $N$ of the same type of [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md), the standard model is fully abstract:

1. $M \sqsubseteq_{PA} N$ if and only if $\mathcal{A}_{PA}[\![M]\!] \sqsubseteq \mathcal{A}_{PA}[\![N]\!]$ (in every environment);
2. $M \simeq_{PA} N$ if and only if $\mathcal{A}_{PA}[\![M]\!] = \mathcal{A}_{PA}[\![N]\!]$.

The direction from denotations to behaviour is computational adequacy for this language. For the converse, if the denotation of closed $M$ is not below that of
closed $N$, then, since the domains are algebraic, there are finite arguments on which $M$ returns a constant $c$ while $N$ does not return $c$ (it may return
nothing); these arguments are definable, and applying $M$ and $N$ to their definitions gives programs of which the first evaluates to $c$ and the second does not. Without the parallel conditional the same model is [not fully abstract](the-scott-model-of-pcf-is-not-fully-abstract.md).

## Depends on

- [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md)

## Proof depends on

- [Finite elements are definable in PCF with the parallel conditional](finite-elements-are-definable-with-parallel.md)

## Expansion

This page becomes ready once:

- Computational adequacy for PCF with the parallel conditional at both ground types: a closed term of ground type whose denotation is a constant $c$ reduces to $c$ (the analogue of Theorem 3.1 of the source below for $\mathcal{L}_{PA}$; proof prerequisite; not yet stated as a page)

## Background

- [Computational adequacy for PCF](../pcf-and-computational-adequacy/adequacy.md): the corresponding result for a sequential PCF with the single ground type of natural numbers

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 4, Theorem 4.3 on page 237 and its proof on page 240, with Theorem 4.1 and the analogue of Theorem 3.1 for $\mathcal{L}_{PA}$.
