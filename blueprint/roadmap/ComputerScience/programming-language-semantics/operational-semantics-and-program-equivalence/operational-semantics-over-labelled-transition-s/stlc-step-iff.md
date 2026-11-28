# Steps of the simply typed λ-calculus semantics are its reductions

Fix a type $A$ of the simply typed λ-calculus. The [operational semantics](stlc.md) on closed terms of type $A$ (terms in the empty context), with a single unit label and values as final configurations, has a step from $x$ to $y$ exactly when the native call-by-value reduction steps from $x$ to $y$: for all closed terms $x, y$ of type $A$, an unlabelled step $x \to y$ of this semantics is equivalent to a call-by-value step $x \to y$.
