# Translation invariance of Lebesgue measure

Let $E \subseteq \mathbb{R}$ be Lebesgue measurable and let $s \in \mathbb{R}$. Then the translate
$E + s = \{x + s : x \in E\}$ is Lebesgue measurable and $m(E + s) = m(E)$, where $m$ is Lebesgue measure.

## Idea

Lebesgue outer measure is defined by covering a set with countably many open intervals, and translating a cover gives a
cover of the translate by intervals of the same lengths, so outer measure is translation invariant for every set. A
Lebesgue measurable set is a Borel set together with a set of outer measure $0$; translation is a homeomorphism, so the
image of a Borel set, its preimage under the inverse translation, is Borel, and translation preserves outer measure $0$,
so it preserves Lebesgue measurability. Up to a constant factor, Lebesgue measure is the only translation-invariant
measure on the Borel sets of $\mathbb{R}$ that is finite on bounded intervals, and Vitali's theorem shows that no
translation-invariant measure defined on all subsets of $\mathbb{R}$ gives every interval its length.

## Statements

- [Translation invariance of Lebesgue measure](lebesgue-translation-invariance.md)

## Background

- [Lebesgue measure on the real line](../lebesgue-measure-on-the-real-line/README.md): the definitions
- [Continuous maps are Borel measurable](../../../measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/README.md): used in the proof

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 2.7, Exercise 8 in Section 2D and Definition 2.73 (version read: the open-access PDF dated 12 June 2026).
