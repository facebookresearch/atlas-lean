# Agreeing numerical renamings coincide on erased terms

Let $\rho$ be a type-preserving
renaming of variables from context $\Gamma$ to context $\Delta$, and let
$r, s : \mathbb{N} \to \mathbb{N}$ both agree with $\rho$: for every variable $x$ of $\Gamma$, the
de Bruijn index of $\rho(x)$ is the image of the index of $x$ under $r$, and also under $s$. Then
for every intrinsically typed term $t$ of type $A$ in context $\Gamma$, renaming the erasure of $t$
by $r$ and renaming it by $s$ give the same raw term.
