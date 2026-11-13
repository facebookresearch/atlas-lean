# Evaluation of a type scheme

Given maps $f$ and $g$ from natural numbers to monotypes
over $B$, a type scheme $\sigma$ over $B$ evaluates to the monotype obtained by replacing each
free type variable $x$ of $\sigma$ by $f(x)$ and each bound variable $i$ by $g(i)$, keeping
every base type $b$ unchanged. An arrow $\sigma_1 \to \sigma_2$ evaluates to the arrow from the
evaluation of $\sigma_1$ to the evaluation of $\sigma_2$.
