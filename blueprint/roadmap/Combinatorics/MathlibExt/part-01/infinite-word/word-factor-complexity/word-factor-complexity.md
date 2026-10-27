---
article_id: af_a69144028a7ad44984a78ca5
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.wordFactorComplexity
---

# Word Factor Complexity

Factor complexity of an infinite word `w` over a finite alphabet:
the complexity function `p_w(n)`, the number of distinct contiguous factors
of `w` of length `n`, where a length-`n` factor starting at `i` is
`fun j : Fin n => w (i + j)`. The image set collapses repeated occurrences,
so `Set.ncard` of the range counts distinct factors rather than occurrences.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Factor Set](../factor/factor-set.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity](../../../../../../sources/v2/MathlibExt.md)
- Fabien Durand, Julien Leroy, and Gwenaël Richomme, *Do the Properties of an S-adic Representation Determine Factor Complexity?*, Journal of Integer Sequences 16 (2013), Article 13.2.6, complexity-function definition, lines 117–128, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Durand/durand2.tex>.
