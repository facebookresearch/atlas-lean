# Hypotheses of a simply typed context

Propositions over a type $B$ of atoms are built from atoms, conjunction, disjunction and implication $\varphi \to \psi$. Simple types over $B$ are read as propositions by sending a base type $b$ to the atom $b$ and a function type $A \Rightarrow C$ to the implication $\lceil A \rceil \to \lceil C \rceil$, where $\lceil A \rceil$ denotes the proposition of $A$.

For a type $B$ of base types with decidable equality and a context $\Gamma$ (a list of simple types over $B$), the hypotheses of $\Gamma$ form the finite set $H(\Gamma) = \{\lceil A \rceil : A \in \Gamma\}$ of propositions. Order and repetitions in $\Gamma$ are forgotten.
