# For signed permutations, signed breakpoints equal doubled breakpoints

For every natural number $n$ and every [signed permutation](svalid.md) $\pi$ of $1, \dots, n$, the
[signed breakpoint count](sbreaks.md) of $\pi$, framed by $0$ and $n + 1$, equals the
[unsigned breakpoint count](ubreaks.md) of its [doubled list](dbl.md), framed by $0$ and $2n + 1$:
$b^{\pm}_n(\pi) = b_{2n}(\delta(\pi))$ (Shamir and Peer, Lecture 11, signed setting). The hypothesis
cannot be dropped: for $n = 1$ and the list $(1, 1)$ the
[two counts differ](sbreaks-eq-ubreaks-dbl-counterex.md).
