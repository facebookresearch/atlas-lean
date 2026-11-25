# Evaluation into the Kripke semantic domain

Let $t$ be a term of type $T$ in context
$\Gamma$ and let $\eta$ be a semantic environment interpreting every variable of $\Gamma$ as a
semantic value in context $\Delta$. The evaluation $\operatorname{ev}(t, \eta)$ is the semantic
value of type $T$ in context $\Delta$ defined by recursion on $t$: a variable $x$ evaluates to
$\eta(x)$; an application $f\,a$ evaluates to the semantic function $\operatorname{ev}(f, \eta)$
applied, along the identity renaming of $\Delta$, to $\operatorname{ev}(a, \eta)$; and an
abstraction $\lambda b$ of type $A \to B$, whose body $b$ lies in the context $\Gamma$ extended
by $A$, evaluates to the semantic function that sends a renaming $\rho$ from $\Delta$ to a context
$\Theta$ and a semantic value $a$ of type $A$ in $\Theta$ to $\operatorname{ev}(b, \eta')$, where
$\eta'$ sends the new variable to $a$ and each variable $x$ of $\Gamma$ to $\eta(x)$ renamed along
$\rho$.
