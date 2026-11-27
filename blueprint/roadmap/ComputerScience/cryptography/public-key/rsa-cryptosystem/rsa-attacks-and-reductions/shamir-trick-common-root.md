# Shamir's trick: a common root from coprime exponents

Let $N > 0$, let $e, f$ be coprime natural numbers, and let $w$ be a unit modulo $N$ with $w^{e} \equiv y^{f} \pmod N$. With $s, t$ such that $es - ft = 1$ (from the extended Euclidean algorithm), $x = y^{s} w^{-t} \bmod N$ satisfies $x^{e} \equiv y \pmod N$; if $y$ is a unit, so is $x$. The computation runs in polynomial time.

## Proof sketch

$x^e = y^{es} w^{-te} = y^{es} y^{-tf} = y^{es - ft} = y$.

## Depends on

- [RSA key](../key.md)

## Sources

- A. Shamir, "On the Generation of Cryptographically Strong Pseudorandom Sequences", ACM Transactions on Computer Systems 1(1), 1983.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
