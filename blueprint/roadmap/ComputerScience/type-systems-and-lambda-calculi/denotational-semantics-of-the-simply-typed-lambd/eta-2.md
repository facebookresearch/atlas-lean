# Eta is sound for the denotational semantics

For every interpretation $I$ of the base
types and every term $f$ of type $A \Rightarrow B$ in a context $\Gamma$, let $f'$ be the
weakening of $f$ to the context $\Gamma$ extended by a newest variable $x$ of type $A$. Then the
term $\lambda x.\, f'\,x$, which binds $x$, is semantically equal to $f$ in $I$ (has the same
denotation in every environment).
