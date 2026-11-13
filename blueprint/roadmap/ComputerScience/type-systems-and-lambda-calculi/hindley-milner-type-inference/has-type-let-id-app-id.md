# `let` generalizes

For every typing context $\Gamma$, all variable names $f$ and $x$, and
every type variable $\alpha$, the expression $\mathtt{let}\ f = \lambda x.\, x\ \mathtt{in}\ f\, f$
has type $\alpha \to \alpha$ in $\Gamma$.
