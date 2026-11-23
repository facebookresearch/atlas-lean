# PCF denotation of a substituted term

Let $\sigma$ be a type-preserving substitution
assigning to each variable of a context $\Gamma$ a PCF term in a context $\Delta$, let $t$ be a
term of type $A$ in context $\Gamma$, and let $\eta$ be an environment for $\Delta$. Then the
denotation at $\eta$ of the term obtained by applying $\sigma$ to $t$ equals the denotation of $t$
at the environment for $\Gamma$ that gives each variable $x$ of $\Gamma$ the value at $\eta$ of the
denotation of $\sigma(x)$.
