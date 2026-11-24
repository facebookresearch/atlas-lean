# Independence of σ-fields, random variables and events

Let $(\Omega, \mathcal F, P)$ be a probability space.

- σ-fields $\mathcal F_1, \dots, \mathcal F_n \subseteq \mathcal F$ are *independent* if
  $P(A_1 \cap \dots \cap A_n) = P(A_1) \cdots P(A_n)$ whenever $A_i \in \mathcal F_i$ for $i = 1, \dots, n$.
- Real random variables $X_1, \dots, X_n$ are *independent* if
  $P(X_1 \in B_1, \dots, X_n \in B_n) = \prod_{i=1}^n P(X_i \in B_i)$ for all Borel sets $B_1, \dots, B_n \subseteq \mathbb R$.
- Events $A_1, \dots, A_n \in \mathcal F$ are *independent* if $P\big(\bigcap_{i \in I} A_i\big) = \prod_{i \in I} P(A_i)$ for
  every $I \subseteq \{1, \dots, n\}$.
- Collections $\mathcal A_1, \dots, \mathcal A_n \subseteq \mathcal F$ of events are *independent* if
  $P\big(\bigcap_{i \in I} A_i\big) = \prod_{i \in I} P(A_i)$ for every $I \subseteq \{1, \dots, n\}$ and every choice of
  $A_i \in \mathcal A_i$ for $i \in I$. For one-element collections $\mathcal A_i = \{A_i\}$ this is independence of
  the events $A_1, \dots, A_n$.

An infinite family of σ-fields, random variables, events or collections of events is independent if every finite
subfamily is independent.

## Depends on

- [Probability measure](../../probability-measures/is-probability-measure.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 2.1 (the definitions of independence) and Section 2.1.1 (independent collections of sets) (version read: the author's January 2019 PDF).
