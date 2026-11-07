# Fraenkel's Bernoulli recurrence for exact covers

Let $q \ge 2$, $m \ge 1$ and $M$ be
natural numbers, and for $i = 1, \dots, q$ let $n_i$ be a positive integer and $a_i$ an integer
with $0 \le a_i < n_i$. Suppose the residue classes $a_i \bmod n_i$, counted with repetition,
form an exact $M$-cover of $\mathbb{Z}$: every integer $k$ satisfies $k \equiv a_i \pmod{n_i}$
for exactly $M$ indices $i$. Then

$$
B_m \Big(M - \sum_{i=1}^{q} n_i^{m-1}\Big) =
\sum_{i=1}^{q} n_i^{m-1} \sum_{s=0}^{m-1} \binom{m}{s} B_s \Big(\frac{a_i}{n_i}\Big)^{m-s},
$$

where $B_s$ is the $s$-th Bernoulli number, with the convention $B_1 = -\frac{1}{2}$.

Only this direction of the source's equation (23) is stated; the converse, Beebee's variant with
a parameter $x$, and Porubsky's weighted variant are not.

## Sources

- Yevgenya Movshovich, "Raabe's Identity and Covering Systems," Journal of Integer Sequences 23 (2020), Article 20.2.8, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Movshovich/movsho5.tex>. Equation (23); exact source span: lines 228–241; full live TeX source-file SHA-256 `24b31e07198371d27b492f46b2d747aa49e9a49323696d6b4a9c18deab8ff593`; exact newline-terminated equation/context span SHA-256 `1c95008be9bbbc150a494df7eef936abd3ee277ab9bd32ff1f67b0b0f4b76526`.
