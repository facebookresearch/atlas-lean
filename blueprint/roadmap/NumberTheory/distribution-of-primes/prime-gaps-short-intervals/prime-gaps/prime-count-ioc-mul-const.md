# Primes in a window of $C$ maximal prime gaps

Let $p_0 = 2 < p_1 = 3 < p_2 = 5 < \dots$
be the primes in increasing order, let $\pi$ be the prime-counting function, and for real $x$
let $d(x)$ be the largest prime gap $p_{n+1} - p_n$ over all $n$ with $p_n < x$, with
$d(x) = 0$ when no prime is less than $x$. For a real number $C$, this is the function on pairs
$(x, y)$ of real numbers given by $\pi(\lfloor y + C\,d(x) \rfloor) - \pi(\lfloor y \rfloor)$,
where the floors are taken in $\mathbb{N}$ (so negative numbers have floor $0$) and the
difference is taken in $\mathbb{R}$.

When $C \ge 0$ this is the number of primes in the interval $(y, y + C\,d(x)]$.
