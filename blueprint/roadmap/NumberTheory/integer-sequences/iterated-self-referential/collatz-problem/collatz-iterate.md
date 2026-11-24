# Iterates of the Collatz map

Let $T : \mathbb{N} \to \mathbb{N}$ be the Collatz map, which
sends $n$ to $n / 2$ if $n$ is even and to $3n + 1$ if $n$ is odd. For natural numbers $k$ and
$n$, the $k$-th Collatz iterate of $n$ is $T^k(n)$, the result of applying $T$ to $n$ exactly $k$
times: $T^0(n) = n$ and $T^{k+1}(n) = T(T^k(n))$.
