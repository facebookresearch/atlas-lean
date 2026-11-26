# Pocklington's criterion for $N = Kp^e + 1$

Let $N$, $K$ and $e$ be natural numbers and
let $p$ be a prime, with $0 < K < p^e$ and $N = Kp^e + 1$. If some natural number $a$ satisfies
$a^{N-1} \equiv 1 \pmod{N}$ and $\gcd\big(a^{(N-1)/p} - 1, N\big) = 1$, where $(N-1)/p$ is the
quotient of $N - 1$ by $p$ rounded down and $a^{(N-1)/p} - 1$ is truncated at $0$, then $N$ is
prime.

Proof: The proof follows Pocklington's standard least-prime-factor order argument, from
Pocklington (1914) as stated by Grau and Oller-Marcen, arXiv:1011.4836v3, lines 60-69.

## Sources

- Pocklington (1914), as stated in Grau and Oller-Marcen, "A primality test for Kp^n+1 numbers", arXiv:1011.4836v3, lines 60-69, which give the complete condition, including gcd(a^((N-1)/p)-1,N)=1. The source's integer witness a ∈ ℤ is represented here by a natural residue representative a : ℕ, using Nat.ModEq and Nat.gcd with natural subtraction in the exponents.
