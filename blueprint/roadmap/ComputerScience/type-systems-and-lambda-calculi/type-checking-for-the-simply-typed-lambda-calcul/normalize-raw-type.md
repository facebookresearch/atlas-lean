# Raw normalization reports the inferred type

Let the base types have decidable
equality, let $\Gamma$ be a context of simple types and let $r$ be a raw term. If normalizing
$r$ in $\Gamma$ succeeds and returns a type $A$ together with a raw term, then type inference
for $r$ in $\Gamma$ returns $A$.
