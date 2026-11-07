# Recurrence for weighted fence tilings of even boards

Let $a$ and $b$ be elements of a
commutative semiring $R$, and let $S_m$ be the weighted number of tilings of an $m$-board, with
cells numbered $1, \dots, m$, by half-squares and $(1/2, 1/2)$-fences, a half-square weighing $a$
in an odd cell and $b$ in an even cell. Then for every even $n \ge 2$,

$$
S_n = b^2 S_{n-1} + (2ab+1) S_{n-2} +
2ab \sum_{j=2}^{n/2} S_{n-2j} + 2b^2 \sum_{j=1}^{n/2-1} S_{n-2j-1}.
$$

## Sources

- Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024, Lemma 2.1, (2.1) (`fq-2024-belaggoun01132024-lem-2.1`).
