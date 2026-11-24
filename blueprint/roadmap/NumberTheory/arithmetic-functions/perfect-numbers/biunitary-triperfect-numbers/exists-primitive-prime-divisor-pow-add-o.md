# Primitive prime factors of $a^n + 1$

Let $a \ge 2$ and $n \ge 1$ be integers with
$(a, n) \ne (2, 3)$, and if $n = 1$ suppose that $a + 1$ is not a power of $2$. Then $a^n + 1$
has a primitive prime factor $p$, that is, a prime $p$ that divides $a^n + 1$ but divides no
$a^m + 1$ with $1 \le m < n$, such that $p \equiv 1 \pmod{2n}$.

The second exception is not in the printed statement: for $a = 3$, $n = 1$ the only prime factor
of $3 + 1 = 4$ is $2 \not\equiv 1 \pmod 2$; the paper's proof applies Lemma 2.3 to
$a^{2n} - 1$, whose exceptions include exactly this case.

## Sources

- Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*, Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 5 (`jis-2025-25.4.5-lem-5`).
