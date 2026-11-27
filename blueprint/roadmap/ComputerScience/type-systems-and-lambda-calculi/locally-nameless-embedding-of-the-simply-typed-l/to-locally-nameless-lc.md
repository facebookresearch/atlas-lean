# Canonical locally nameless embeddings are locally closed

The embedding with names $\mathit{names}$ of an intrinsically typed term $t$ is $\mathrm{tr}_{0,\mathit{names}}$ applied to the erasure of $t$ (variables replaced by their de Bruijn positions in the context, lambdas keeping their parameter types); the canonical embedding $t^{\mathrm{LN}}$ uses $\mathit{names} = [0, 1, \dots, |\Gamma| - 1]$ for a term in context $\Gamma$.

For every context $\Gamma$, simple type $A$ and term $t$ of type $A$ in $\Gamma$, including open terms, $t^{\mathrm{LN}}$ is locally closed: in the inductive sense where every free variable is locally closed, an application of two locally closed terms is locally closed, and $\mathrm{abs}\,e$ is locally closed when $e$ opened with $\mathrm{fvar}\,x$ is locally closed for every name $x$ outside some finite set.
