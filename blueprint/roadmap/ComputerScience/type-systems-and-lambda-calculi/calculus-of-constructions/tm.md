# Terms of the calculus of constructions

A term is a variable $\#i$ with de Bruijn index
$i \in \mathbb{N}$, a sort $s$ (either $\mathrm{Prop}$ or $\mathrm{Type}_i$ for some
$i \in \mathbb{N}$), an application $f\,a$ of a term $f$ to a term $a$, an abstraction
$\lambda (x : A).\, b$ with domain $A$ and body $b$, or a dependent product
$\Pi (x : A).\, B$ with domain $A$ and codomain $B$.

In the body of an abstraction or the codomain of a product, index $0$ refers to the bound
variable and index $i + 1$ to the variable that has index $i$ outside the binder.
