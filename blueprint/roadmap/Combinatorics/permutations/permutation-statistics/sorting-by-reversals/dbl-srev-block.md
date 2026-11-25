# On signed permutations, doubling turns signed into unsigned reversals

For a natural number $n$, a [signed permutation](svalid.md) $\pi$ of $1, \dots, n$, with positions
counted from $0$, and natural numbers $i \le j$ with $j$ less than the length $n$ of $\pi$, the
[doubled list](dbl.md) of the [signed reversal](srev-block.md) of positions $i$ to $j$ is the
[reversal](rev-block.md) of positions $2i$ to $2j + 1$ of the doubled list:
$\delta(\operatorname{rev}^{\pm}_{i,j}(\pi)) = \operatorname{rev}_{2i,\,2j+1}(\delta(\pi))$ (Shamir
and Peer, Lecture 11, signed setting). The hypothesis matters through the nonzero entries: for
$x \ne 0$ the doubled pair of $-x$ is that of $x$ reversed, which fails for $x = 0$, since $-0 = 0$
and $\delta(0) = (-1, 0)$. For example, for the list $(0, 1)$ and $i = j = 0$ the two sides are
$(-1, 0, 1, 2)$ and $(0, -1, 1, 2)$.
