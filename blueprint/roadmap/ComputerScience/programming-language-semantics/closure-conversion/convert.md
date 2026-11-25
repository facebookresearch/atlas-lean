# Closure conversion with accessors

Let $\mathit{acc}$ be a family of target terms indexed
by the natural numbers (accessor $i$ fetches source variable $i$) and $n$ a natural number (the
number of source variables in scope). The conversion $\mathcal{C}(\mathit{acc}, n, t)$ of a
source term $t$ is defined by recursion on $t$. A variable $i$ converts to $\mathit{acc}(i)$. A
lambda with body $b$ (whatever its parameter type) converts to the pair of
$\mathsf{code}\,\mathcal{C}(c, n + 1, b)$, where $c$ is the family of code accessors, and the
target term packing $\mathit{acc}(0), \dots, \mathit{acc}(n - 1)$ as nested pairs ending in
$\mathsf{unit}$. An application $f\,a$ converts to
$\mathsf{let}\ \mathcal{C}(\mathit{acc}, n, f)\ \mathsf{in}\ (\mathsf{fst}\,\#0)\,
(\mathcal{C}(\mathit{acc}', n, a), \mathsf{snd}\,\#0)$, where $\#0$ is the target variable $0$
and $\mathit{acc}'(i)$ is the shift of $\mathit{acc}(i)$ for every $i$.
