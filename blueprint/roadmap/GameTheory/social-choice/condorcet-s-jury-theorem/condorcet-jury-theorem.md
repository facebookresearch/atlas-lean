# Condorcet's jury theorem

Let $\mu$ be a probability measure on a measurable space
$\Omega$, let $X_0, X_1, \dots$ be measurable maps from $\Omega$ to $\{\text{true}, \text{false}\}$
(the votes, true meaning a correct vote), and let $p$ be a number with $1/2 < p < 1$. Suppose that
each vote is correct with probability $p$, that is $\mu(X_i = \text{true}) = p$ for every $i$, and
that the events $\{X_i = \text{true}\}$ are independent: for every nonempty finite set $s$ of
indices, $\mu\bigl(\bigcap_{i \in s} \{X_i = \text{true}\}\bigr) = \prod_{i \in s}
\mu(X_i = \text{true})$. For $n \in \mathbb{N}$ let $M_n$ be the event that more than
$\lfloor n/2 \rfloor$ of the first $n$ votes $X_0, \dots, X_{n-1}$ are correct. Then
$\mu(M_n) \to 1$ as $n \to \infty$, and $\mu(M_n) > p$ for every odd $n > 1$.

## Sources

- https://en.wikipedia.org/wiki/Condorcet%27s_jury_theorem. Proves `Wanted` entry `condorcet_jury_theorem`.
