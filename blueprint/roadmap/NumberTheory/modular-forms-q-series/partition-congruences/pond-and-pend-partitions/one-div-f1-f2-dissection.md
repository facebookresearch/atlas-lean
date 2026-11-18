# 3-dissection of $1 / (f_1 f_2)$

Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the
Euler products in $\mathbb{Z}[[q]]$. Then
$f_3^6 f_6^6 f_9^3 f_{18}^3 = f_1 f_2 f_6^4 f_9^{12} + q f_1 f_2 f_3 f_6^3 f_9^9 f_{18}^3 +
3 q^2 f_1 f_2 f_3^2 f_6^2 f_9^6 f_{18}^6 - 2 q^3 f_1 f_2 f_3^3 f_6 f_9^3 f_{18}^9 +
4 q^4 f_1 f_2 f_3^4 f_{18}^{12}$.

Since each $f_k$ with $k \ge 1$ has constant term $1$, dividing both sides by
$f_1 f_2 f_3^6 f_6^6 f_9^3 f_{18}^3$ shows that this is equivalent to
$1 / (f_1 f_2) = f_9^9 / (f_3^6 f_6^2 f_{18}^3) + q f_9^6 / (f_3^5 f_6^3) +
3 q^2 f_9^3 f_{18}^3 / (f_3^4 f_6^4) - 2 q^3 f_{18}^6 / (f_3^3 f_6^5) +
4 q^4 f_{18}^9 / (f_3^2 f_6^6 f_9^3)$.

## Sources

- James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*, Journal of Integer Sequences 27 (2024), Article 24.4.7, Lemma 9 (`jis-2024-24.4.7-lem-9`).
