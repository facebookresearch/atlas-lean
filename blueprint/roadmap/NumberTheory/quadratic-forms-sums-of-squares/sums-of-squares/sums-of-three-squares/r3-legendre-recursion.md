# Legendre-symbol recursion for three-square counts

For a natural number $m$, let $r_3(m)$
denote the number of ordered triples of integers $(x, y, z)$ with $x^2 + y^2 + z^2 = m$. Let
$p \ge 3$ be a prime and let $n \ge 1$ and $\alpha \ge 0$ be natural numbers. Then

$$
r_3(p^{2\alpha} n) = \left(\frac{p^{\alpha+1} - 1}{p - 1} - \left(\frac{-n}{p}\right)
\frac{p^{\alpha} - 1}{p - 1}\right) r_3(n) - p \, \frac{p^{\alpha} - 1}{p - 1} \, r_3(n/p^2),
$$

where $\left(\frac{-n}{p}\right)$ is the Legendre symbol, both quotients by $p - 1$ are exact
integer divisions, and the term $r_3(n/p^2)$ is read as $0$ when $p^2$ does not divide $n$.

Proof: The route is an elementary p-neighbour double count using quaternionic descent and
finite-field conic counts, followed by a two-step induction on the exponent.

## Sources

- Liuquan Wang, "Another Proof of a Conjecture by Hirschhorn and Sellers on Overpartitions", Journal of Integer Sequences 17 (2014), Article 14.9.8, Lemma `r3relation`, lines 228-232, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Wang2/wang15.tex>.
