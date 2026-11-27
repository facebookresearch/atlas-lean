# The asynchronous convergence theorem

In the [totally asynchronous iteration model](the-totally-asynchronous-iteration-model.md), suppose there are subsets $X^0, X^1, X^2, \dots$ of $X$ such that:

1. every sequence $(x^k)$ with $x^k \in X^k$ for all $k$ converges coordinatewise to one fixed point $x^*$ of $f$;
2. each $X^k$ is closed under a computation at a single node: $x \in X^k$ implies $f(x; j) \in X^k$, where $f(x; j)$ replaces the coordinates in $I_j$ by $f_i(x)$ and keeps the others;
3. each $X^k$ is closed under a single communication: $x, x' \in X^k$ implies $C(x, x'; j) \in X^k$, where $C(x, x'; j)$ takes the coordinates in $I_j$ from $x'$ and the others from $x$;
4. a synchronous round moves $X^k$ into $X^{k+1}$: if $x^1, \dots, x^n \in X^k$, then the vector $F$ with $F_i = f_i(x^j)$ for $i \in I_j$ lies in $X^{k+1}$.

If the initial buffer contents of every node lie in $X^0$, then $\lim_{t \to \infty} x^t_i(j) = x^*_i$ for every coordinate $i$ and node $j$. Conditions 1 and 4 alone give convergence of the synchronous iteration; 2 and 3 make the sets robust to arbitrary interleavings.

## Depends on

- [The totally asynchronous iteration model](the-totally-asynchronous-iteration-model.md)

## Sources

- D. P. Bertsekas, "Distributed asynchronous computation of fixed points", *Mathematical Programming* 27:107–120, 1983; <https://web.mit.edu/dimitrib/OldFiles/www/Distr_Comp_Fixed.pdf>, Section 3, Assumption B (conditions (a)–(d), equations (10)–(16)) and the Proposition with its proof.
