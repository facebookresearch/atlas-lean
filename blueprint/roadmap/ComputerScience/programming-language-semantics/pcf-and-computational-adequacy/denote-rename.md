# PCF denotation of a renamed term

Let $\rho$ be a type-preserving renaming of the
variables of a context $\Gamma$ into a context $\Delta$, let $t$ be a PCF term of type $A$ in
context $\Gamma$, and let $\eta$ be an environment for $\Delta$. Then the denotation at $\eta$ of
the renaming of $t$ along $\rho$ equals the denotation of $t$ at the environment for $\Gamma$ that
gives each variable $x$ of $\Gamma$ the value of the variable $\rho(x)$ in $\eta$.
