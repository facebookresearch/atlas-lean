# Parity of iterated horizontal sums of a Delannoy array with binomial seeds

Let $R(m, n)$,
for $m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for
all $m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for
the $i$-fold horizontal sum, so $R^0 = R$. Let $k \in \mathbb{N}$ and suppose
$R(0, n) = \binom{k+n}{k}$ for all $n$; the values $R(m, 0)$ for $m \ge 1$ are arbitrary. Then
every entry of $R^{k+1}$ is even, and for every $j \le k$ some entry of $R^j$ is odd.

## Sources

- Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal of Integer Sequences 27 (2024), Article 24.1.8, Lemma 16 (`jis-2024-24.1.8-lem-16`).
