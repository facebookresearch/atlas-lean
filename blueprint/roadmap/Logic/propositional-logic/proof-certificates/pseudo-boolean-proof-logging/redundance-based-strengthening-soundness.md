# Soundness of redundance-based strengthening with witnesses

Let $\mathcal{D}$ be a set of pseudo-Boolean constraints, $C$ a constraint and $\omega$ a *witness*: a substitution mapping each variable to $0$, $1$ or a literal. Write $D\restriction_\omega$ for the constraint obtained by applying $\omega$ (so $\sigma$ satisfies $D\restriction_\omega$ iff $\sigma \circ \omega$ satisfies $D$). If $\mathcal{D} \cup \{\neg C\}$ implies $D\restriction_\omega$ for every $D \in \mathcal{D} \cup \{C\}$ (checked by cutting planes or RUP), then $\mathcal{D}$ and $\mathcal{D} \cup \{C\}$ are equisatisfiable; in optimization, if additionally the objective does not increase under $\omega$, adding $C$ preserves the optimal value. This rule generalizes RAT and can break a single symmetry; the dominance-based strengthening rule of Bogaerts et al. extends it to reasoning that redundance alone cannot express, such as breaking several symmetries at once.

## Proof sketch

Given a model $\sigma$ of $\mathcal{D}$ violating $C$, the assignment $\sigma \circ \omega$ satisfies every constraint of $\mathcal{D}$ and $C$ by the implication hypotheses.

## Depends on

- [Pseudo-Boolean constraints in normalized form](pseudo-boolean-constraints.md)

## Proof depends on

- [Reverse unit propagation for pseudo-Boolean constraints](pseudo-boolean-reverse-unit-propagation.md)

## Sources

- B. Bogaerts, S. Gocht, C. McCreesh and J. Nordström, "Certified Dominance and Symmetry Breaking for Combinatorial Optimisation", Journal of Artificial Intelligence Research 77, 1539–1589, 2023: Section 3.3, Definition 6 and Proposition 7.
- S. Gocht and J. Nordström, "Certifying Parity Reasoning Efficiently Using Pseudo-Boolean Proofs", Proceedings of the 35th AAAI Conference on Artificial Intelligence, 2021.
