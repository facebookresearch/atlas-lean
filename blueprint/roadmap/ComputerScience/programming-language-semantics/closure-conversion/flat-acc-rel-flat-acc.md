# Flat accessors implement the variables of a closure body

Let $b$ be a raw term, let
$c = (c_0, \dots, c_{m-1})$ be the list of variables captured by $\lambda. b$, let $\rho$ be a list
of source values of length $|\rho|$, write $\rho_n$ for the entry of $\rho$ at index $n$ (counting
from $0$), and let $w_0, \dots, w_{m-1}$ be target values such that $c_k < |\rho|$ and $\rho_{c_k}$
is related to $w_k$ by the flat value relation for every $k < m$. If a source value $v$ is related
to a target value $w$ by the flat value relation, then the flat accessors for $c$ implement the
free variables of $b$ for the source environment $v :: \rho$ (the list $\rho$ with $v$ added at
index $0$) in the one-entry target environment $[(w, \mathrm{enc}(w_0, \dots, w_{m-1}))]$, where
$\mathrm{enc}$ encodes a list of target values as nested pairs ending in $\mathsf{unit}$. That is,
for every free variable $i$ of $b$, $i < |\rho| + 1$ and the flat accessor for $i$ evaluates in
that target environment to a target value related to the entry of $v :: \rho$ at index $i$ by the
flat value relation.
