# Waterhouse's theorem on Frobenius traces

Let $p$ be a prime, let $a \ge 1$, and let $F$
be a finite field with $q = p^a$ elements. An integer $\beta$ is the Frobenius trace
$q + 1 - \#E(F)$ of some elliptic curve $E$ over $F$ if and only if $\beta^2 \le 4q$ and one of
the following holds:
1. $\gcd(\beta, p) = 1$;
2. $a$ is even and $\beta = \pm 2p^{a/2}$;
3. $a$ is even, $p \not\equiv 1 \pmod 3$ and $\beta = \pm p^{a/2}$;
4. $a$ is odd, $p = 2$ or $p = 3$, and $\beta = \pm p^{(a+1)/2}$;
5. $a$ is odd, or $a$ is even and $p \not\equiv 1 \pmod 4$, and $\beta = 0$.

The paper states a one-to-one correspondence between $F$-isogeny classes of elliptic curves and
these integers; the statement above describes its image. Injectivity is Tate's isogeny theorem.

## Sources

- Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two Vertices*, INTEGERS 24 (2024), Article A8, Theorem 6 (`integers-2024-A8-thm-6`).
