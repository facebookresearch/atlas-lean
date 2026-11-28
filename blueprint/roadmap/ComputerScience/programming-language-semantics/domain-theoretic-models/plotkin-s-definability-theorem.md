# Plotkin's definability theorem

Extend [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md) by a constant $\exists : (\iota \to o) \to o$ denoting the
[continuous existential](the-continuous-existential-is-not-definable.md), with reductions $\exists F \to \mathit{ff}$ if $F\, \Omega \to^* \mathit{ff}$ and $\exists F \to \mathit{tt}$ if $F\, k_m \to^* \mathit{tt}$ for some
$m \ge 0$; call the result $\mathcal{L}_{PA+\exists}$. Then an element of a domain $D_\sigma$ of the standard model is
[computable](computable-elements-of-the-pcf-model.md) if and only if it is the denotation of a closed term of $\mathcal{L}_{PA+\exists}$.

The proof defines approximations to the apartness relation $x \mathrel{\#} y$ (no upper bound) by terms and combines them with primitive recursive
enumerations of finite elements; only recursion operators of level 3 are needed, and $\exists$ only to define elements of level at least 2.

## Depends on

- [The continuous existential is not definable in PCF with the parallel conditional](the-continuous-existential-is-not-definable.md)
- [Computable elements of the PCF model](computable-elements-of-the-pcf-model.md)

## Proof depends on

- [Finite elements are definable in PCF with the parallel conditional](finite-elements-are-definable-with-parallel.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 5, Theorem 5.1 (definability theorem), Lemma 5.2 and the proof on pages 251–253, and the reduction rules for $\exists$ on page 254.
