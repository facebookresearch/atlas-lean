# State of the conjugate gradient method

A state of the conjugate gradient method in $\mathbb{R}^n$ is a triple $(x, r, d)$ of vectors of
$\mathbb{R}^n$: the current iterate $x$, the residual $r$ and the search direction $d$. The
definition places no constraint on the triple. For a system $Ax = b$, the
[initial state](init.md) has $r = b - Ax$, and the [conjugate gradient step](step.md) preserves
this relation: it replaces $x$ by $x + \alpha d$ and $r$ by $r - \alpha A d$.
