# Call-by-value CPS translation of types

For a fixed answer type $R$, the translation
$\overline{A}$ of a simple type $A$ is defined by recursion on $A$: $\overline{b} = b$ for a base
type $b$, and $\overline{A \to B} = \overline{A} \to ((\overline{B} \to R) \to R)$.
