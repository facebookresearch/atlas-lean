# Weakening for let-polymorphic typing

Let $\Gamma \vdash e : \tau$, and let $\Gamma'$ be
a context in which every free name $y$ of $e$ that has a scheme $\sigma$ in $\Gamma$ has a scheme
in $\Gamma'$ more general than $\sigma$. Then $\Gamma' \vdash e : \tau$. The context $\Gamma'$
may bind other names and have other free type variables; at each `let` of $e$, the type
variables generalized in $\Gamma$ are renamed above the free type variables of $\Gamma'$.
