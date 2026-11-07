# Joint recurrence for $\mathcal{M}_1$ and its nested companion

Read the values of the
meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$, write $\oplus$ for addition modulo $2$,
and let $b(m) = \mathcal{M}_1(2m + 1 - \mathcal{M}_1(m))$ for every $m \in \mathbb{N}$. Then for
every $n \ge 1$, with $x = \mathcal{M}_1(n)$ and $y = b(n)$, the pairs
$s(k) = (\mathcal{M}_1(k), b(k))$ satisfy $s(4n) = (x, y)$, $s(4n+1) = (1 \oplus x, x \oplus y)$,
$s(4n+2) = (y, 1 \oplus x)$ and $s(4n+3) = (1 \oplus y, 1 \oplus x \oplus y)$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Lemma 12 (`jis-2026-26.4.1-lem-12`).
