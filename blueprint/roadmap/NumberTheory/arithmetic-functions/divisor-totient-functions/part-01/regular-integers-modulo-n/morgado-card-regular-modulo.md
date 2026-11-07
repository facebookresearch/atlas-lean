# Morgado's formula for the number of regular residues

Let $n$ be a positive integer. Call
a residue class $m \in \mathbb{Z}/n\mathbb{Z}$ regular if the equation $m^2 x = m$ has a solution
$x \in \mathbb{Z}/n\mathbb{Z}$, and let $\varrho(n)$ be the number of regular residue classes. Let
$U(n)$ be the set of positive divisors $d$ of $n$ with $\gcd(d, n/d) = 1$. Then

$$\varrho(n) = \sum_{d \in U(n)} \varphi(d),$$

where $\varphi$ is Euler's totient function.

The sequence $\varrho(1), \varrho(2), \ldots$ is OEIS A055653.

## Sources

- Klaus Dohmen and Mandy Lange-Geisler, "On the Number of Regular Integers Modulo n and Its Significance for Cryptography", Journal of Integer Sequences 29 (2026), Article 26.2.4, Definition [Morgado 1972] lines 108-112 and Theorem [Morgado 1972] (equation `eq:2`) lines 127-132: https://cs.uwaterloo.ca/journals/JIS/VOL29/Dohmen/dohmen4.tex The formula is attributed to J. Morgado (1972). It follows from `ncard_regular_eq_sum_totient_unitaryDivisors`; the filter spells out `n.unitaryDivisors` and keeps the source's shape.
