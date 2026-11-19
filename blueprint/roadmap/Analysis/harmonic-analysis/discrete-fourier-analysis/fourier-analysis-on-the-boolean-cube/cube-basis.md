# Lagrange basis polynomial of a cube point

Let $x$ be a point of the Boolean cube in $n$
coordinates, indexed by $i \in \{0, \dots, n-1\}$. Its cube basis polynomial is the real
polynomial $\prod_{i=0}^{n-1} \ell_i$ in the variables $X_0, \dots, X_{n-1}$, where $\ell_i = X_i$
if $x_i$ is true and $\ell_i = 1 - X_i$ if $x_i$ is false. Reading true as $1$ and false as $0$,
it is the Lagrange basis polynomial of $x$ on the grid $\{0,1\}^n$.
