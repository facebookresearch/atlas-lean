# The simply typed λ-calculus semantics is deterministic

Fix a type $A$ of the simply typed λ-calculus, and consider the [operational semantics](stlc.md) on closed terms of type $A$ (terms in the empty context), whose unlabelled steps are the call-by-value reduction steps. This semantics is deterministic: if a closed term $x$ of type $A$ steps to $y$ and to $z$, then $y = z$.
