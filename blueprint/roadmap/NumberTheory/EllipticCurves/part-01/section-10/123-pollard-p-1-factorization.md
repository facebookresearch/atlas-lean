---
article_id: af_abf0559d18284171e122e282
declaration: def
origin: cited
statement: formalized
lean: PollardPM1.pollardPM1
---

# Algorithm 10.8 (Pollard p−1 factorization)

Input: An integer $N$ to be factored and a smoothness bound $B$. Output: A proper divisor of $N$ or failure.
1. Pick a random integer $a \in [1, N-1]$.
2. If $d = \gcd(a, N)$ is not $1$ then return $d$.
3. Set $b = a$ and for each prime $\ell \leq B$:
   a. Set $b = b^{\ell^e} \bmod N$, where $\ell^{e-1} < N \leq \ell^e$. If $b = 1$ then return failure.
   b. If $d = \gcd(b-1, N)$ is not $1$ then return $d$.
4. Return failure.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 10.5](../../../../../sources/v1/EllipticCurves.md)
