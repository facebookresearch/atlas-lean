# Evaluation respects pointwise equal environments

Let $t$ be a term of type $A$ in
context $\Gamma$, and let $\xi$ and $\zeta$ be semantic environments interpreting the variables of
$\Gamma$ in a context $\Delta$. If $\xi(x) = \zeta(x)$ for every variable $x$ of $\Gamma$, of any
type, then evaluating $t$ in $\xi$ and evaluating $t$ in $\zeta$ give the same semantic value.
