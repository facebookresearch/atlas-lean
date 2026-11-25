# Semantic equality is a congruence for lambda abstraction

Fix an interpretation $I$ of
the base types. If two terms of type $B$ in the context $\Gamma$ extended by a newest variable
of type $A$ are semantically equal in $I$ (they have the same denotation in every environment),
then their lambda abstractions, terms of type $A \Rightarrow B$ in $\Gamma$, are semantically
equal in $I$.
