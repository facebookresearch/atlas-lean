# Progress for closed terms

Every term $t$ of type $A$ in the empty context is either a
value or reduces in one call-by-value step to some term $t'$. Together with preservation, which
holds by construction because `Step` relates terms of the same type, this is the type safety
theorem of the calculus.
