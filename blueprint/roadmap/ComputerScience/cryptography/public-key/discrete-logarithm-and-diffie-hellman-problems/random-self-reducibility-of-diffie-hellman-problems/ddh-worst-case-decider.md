# An average-case DDH distinguisher yields a worst-case decider

In a fixed group of prime order $q$, let $D$ be a DDH distinguisher with advantage at least $\varepsilon = 1/\mathrm{invEps}(n)$, $\mathrm{invEps}$ polynomial-time computable. Then there is a probabilistic polynomial-time algorithm that, for every triple $(u, v, w)$, decides whether it is a Diffie–Hellman triple with error probability at most $e^{-n}$; it runs $D$ on $N = O(n \cdot \mathrm{invEps}(n)^2)$ rerandomized copies of the input and of known real and random triples, and compares the acceptance frequencies.

## Proof sketch

By full rerandomization (randomizing $u$ as well), $D$'s acceptance probability on the rerandomized input equals its acceptance probability on real triples or on random triples. Estimating the three frequencies to accuracy $\varepsilon/3$ by Hoeffding's inequality decides which case holds.

## Depends on

- [Advantage of a DDH distinguisher](../../elgamal-encryption/ddh-advantage.md)

## Proof depends on

- [Rerandomization of DDH triples with a fixed first coordinate](ddh-triple-rerandomization.md)
- [Hoeffding's inequality for averages of bounded variables](../../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Naor and O. Reingold, "Number-Theoretic Constructions of Efficient Pseudo-Random Functions", Journal of the ACM 51(2), 2004.
