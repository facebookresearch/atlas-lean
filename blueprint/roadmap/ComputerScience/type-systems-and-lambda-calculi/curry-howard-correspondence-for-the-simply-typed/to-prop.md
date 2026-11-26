# Simple types as implicational propositions

Propositions over a type $B$ of atoms are built from atoms, conjunction, disjunction and implication $\varphi \to \psi$.

For a type $B$ of base types, every simple type $A$ over $B$ is sent to a proposition $\lceil A \rceil$ over atoms $B$ by recursion: a base type $b$ goes to the atom $b$, and a function type $A \Rightarrow C$ goes to the implication $\lceil A \rceil \to \lceil C \rceil$. The image lies in the implicational fragment.
