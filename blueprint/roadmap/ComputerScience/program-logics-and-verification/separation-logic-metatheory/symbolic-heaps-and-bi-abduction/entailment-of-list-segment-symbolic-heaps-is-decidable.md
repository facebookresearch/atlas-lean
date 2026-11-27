# Entailment of list-segment symbolic heaps is decidable

Validity of an entailment $\Pi \mid \Sigma \vdash \Pi' \mid \Sigma'$ between [symbolic heaps with list segments](symbolic-heaps-with-list-segments.md) is decidable, and in coNP. Satisfaction of a symbolic heap by a given state is decidable in time linear in the sizes of the state and the formula. When the antecedent has no list segments, every model has a heap with as many cells as the antecedent has points-to formulas, and the fragment is closed under renaming of l-values, so it suffices to check finitely many canonical states; the unroll-collapse rule eliminates list segments from the antecedent. Invalidity is witnessed by a counter-model of bounded size, which can be guessed and checked in polynomial time.

## Depends on

- [Symbolic heaps with list segments](symbolic-heaps-with-list-segments.md)
- [The class coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [The unroll-collapse rule is sound](unroll-collapse-rule-is-sound.md)

## Sources

- J. Berdine, C. Calcagno and P. W. O'Hearn, "A decidable fragment of separation logic", *FSTTCS 2004*, LNCS 3328, Springer, 2004, pp. 97–109; extended version <https://jberdine.github.io/pub/2004_fsttcs.pdf>, Section 3, Lemma 1, Lemma 3, Corollary 4 and the discussion of coNP membership after it.
