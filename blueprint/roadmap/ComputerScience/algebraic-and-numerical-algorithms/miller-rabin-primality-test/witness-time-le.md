# Cost of the Miller–Rabin witness test

For natural numbers $a$ and $n$, write
$n - 1 = 2^t u$ with $u$ odd (here $n - 1$ is truncated at $0$, and $t = u = 0$ when $n \le 1$).
The cost of the witness test on base $a$ and modulus $n$ is at most the cost of the modular
exponentiation of $a$ to the power $u$ modulo $n$ plus $t$: at most one multiplication for each
of the $t$ squarings.
