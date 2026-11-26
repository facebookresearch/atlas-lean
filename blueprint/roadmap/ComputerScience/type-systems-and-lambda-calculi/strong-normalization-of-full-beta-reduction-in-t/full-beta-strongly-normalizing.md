# Strong normalization of full beta reduction in the simply typed lambda calculus

Full beta reduction on intrinsically typed terms of type $A$ in a context $\Gamma$ contracts any redex $(\lambda b)\,a \to b[a]$ (no value restriction, $b[a]$ replacing the newest variable of $b$ by $a$) and is closed under both application positions and under lambdas.

For every context $\Gamma$, simple type $A$ and term $t$ of type $A$ in $\Gamma$, $t$ is strongly normalizing (accessible for the converse relation) for full beta reduction on terms of type $A$ in $\Gamma$.
