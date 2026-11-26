# Nested indices in balanced binary sequences

Let $a : \mathbb{N} \to \{0, 1\}$ satisfy
$a(2n) + a(2n+1) = 1$ for every $n \in \mathbb{N}$, and write $\oplus$ for addition modulo $2$.
Then for every $n \in \mathbb{N}$, $a(2n + a(n)) = a(2n) \oplus a(n)$ and
$a(2n + 1 - a(n)) = a(2n+1) \oplus a(n)$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Lemma 5 (`jis-2026-26.4.1-lem-5`).
