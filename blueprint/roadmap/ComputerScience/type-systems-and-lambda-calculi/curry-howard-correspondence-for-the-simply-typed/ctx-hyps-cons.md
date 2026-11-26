# Extending a context adds one hypothesis

Propositions over a type $B$ of atoms are built from atoms, conjunction, disjunction and implication $\varphi \to \psi$. Simple types over $B$ are read as propositions by sending a base type $b$ to the atom $b$ and a function type $A \Rightarrow C$ to the implication $\lceil A \rceil \to \lceil C \rceil$, where $\lceil A \rceil$ denotes the proposition of $A$. For base types with decidable equality, the hypotheses $H(\Gamma)$ of a context $\Gamma$ (a list of simple types) are the finite set $\{\lceil A \rceil : A \in \Gamma\}$.

For every simple type $A$ and context $\Gamma$, $H(A :: \Gamma) = \{\lceil A \rceil\} \cup H(\Gamma)$.
