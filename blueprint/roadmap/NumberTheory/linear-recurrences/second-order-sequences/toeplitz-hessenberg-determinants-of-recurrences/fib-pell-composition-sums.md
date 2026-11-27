# Composition-sum formulas for $F_{2n}$, $F_{3n-1}$ and $P_{n-1}$

Let $F_k$ be the
Fibonacci numbers and $P_k$ the Pell numbers. For every $n \ge 1$, with each sum running over all
compositions $(c_1, \dots, c_r)$ of $n$ (tuples of positive integers with
$c_1 + \dots + c_r = n$),
$F_{2n} = \sum \prod_{i=1}^{r} c_i$,
$F_{3n-1} = 2^{n-1} \sum \prod_{i=1}^{r} \frac{2 c_i - 1}{2^{c_i - 1}}$ and
$P_{n-1} = 2^{n-1} \sum \prod_{i=1}^{r} \frac{c_i - 1}{2^{c_i - 1}}$.

In the last sum only compositions with no part equal to $1$ contribute; the source writes it as
a multinomial sum over $2s_1 + 3s_2 + \dots + n s_{n-1} = n$.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Proposition 1.
