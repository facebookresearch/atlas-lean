# Full abstraction of PCF with the parallel conditional and the existential

For $\mathcal{L}_{PA+\exists}$, [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md) and the [continuous existential](plotkin-s-definability-theorem.md):

1. reduction is Church–Rosser, and a program $M$ evaluates to a constant $c$ exactly when its denotation in the standard model is $c$;
2. the standard model is fully abstract: $M \sqsubseteq_{PA+\exists} N$ if and only if $\mathcal{A}_{PA+\exists}[\![M]\!] \sqsubseteq \mathcal{A}_{PA+\exists}[\![N]\!]$, and likewise
   for equivalence.

Together with the [definability theorem](plotkin-s-definability-theorem.md) this gives a language whose operational semantics and standard denotational
semantics agree and in which every computable element is definable.

## Depends on

- [Plotkin's definability theorem](plotkin-s-definability-theorem.md)

## Proof depends on

- [Full abstraction of PCF with the parallel conditional](full-abstraction-of-pcf-with-the-parallel.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 5, the operational semantics of $\mathcal{L}_{PA+\exists}$ (rules 18, III1 and III2), the computability lemma for $\exists$ and the extension of Theorem 4.3 on page 254.
