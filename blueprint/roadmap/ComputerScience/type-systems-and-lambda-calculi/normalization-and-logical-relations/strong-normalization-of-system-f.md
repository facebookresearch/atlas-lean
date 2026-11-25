# Strong normalization of System F

Every well-typed term of System F is strongly normalizing under full $\beta$-reduction for term and type abstractions. Girard's proof interprets types by reducibility candidates and shows the fundamental lemma: a well-typed term, with its free variables replaced by terms in the interpretations of their types, lies in the interpretation of its type; CR1 then gives strong normalization.

## Depends on

- [Girard's reducibility candidates](girard-s-reducibility-candidates.md)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapter 14
- Original proof: J.-Y. Girard, *Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur*, thèse d'État, Université Paris 7, 1972. The proof by reducibility candidates follows Girard, Lafont and Taylor, Chapter 14.
