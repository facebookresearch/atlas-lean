# Translation invariance of Lebesgue measure

Let $m$ be Lebesgue measure on $\mathbb{R}$, defined on the Lebesgue measurable sets, let
$E \subseteq \mathbb{R}$ be Lebesgue measurable and let $s \in \mathbb{R}$. Then the translate
$E + s = \{x + s : x \in E\}$ is Lebesgue measurable and $m(E + s) = m(E)$.

## Proof

Write $m^*$ for Lebesgue outer measure. If open intervals $I_1, I_2, \ldots$ cover a set $A \subseteq \mathbb{R}$, then
the open intervals $I_k + s$ cover $A + s$ and have the same lengths, so $m^*(A + s) \le m^*(A)$; applying this to
$A + s$ and $-s$ gives $m^*(A + s) = m^*(A)$ for every $A \subseteq \mathbb{R}$. Since $E$ is Lebesgue measurable, there
is a Borel set $B \subseteq E$ with $m^*(E \setminus B) = 0$. The map $x \mapsto x - s$ is continuous, hence Borel
measurable, so $B + s$, the preimage of $B$ under this map, is a Borel set. It is contained in $E + s$, and
$(E + s) \setminus (B + s) = (E \setminus B) + s$ has outer measure $m^*(E \setminus B) = 0$. So $E + s$ is Lebesgue
measurable, and $m(E + s) = m^*(E + s) = m^*(E) = m(E)$.

## Depends on

- [Lebesgue measure on the real line](../lebesgue-measure-on-the-real-line/lebesgue-measure.md)

## Proof depends on

- [Continuous maps are Borel measurable](../../../measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/borel-measurable.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 2.7, Exercise 8 in Section 2D and Definition 2.73 (version read: the open-access PDF dated 12 June 2026).
