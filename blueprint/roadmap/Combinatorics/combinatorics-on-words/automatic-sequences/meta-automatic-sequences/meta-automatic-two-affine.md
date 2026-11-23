# Pair recurrence and $4$-automaticity of $\mathcal{M}_2$

Read the meta-automatic
sequence $\mathcal{M}_2$ as taking values in $\{0, 1\}$, write $\oplus$ for addition modulo $2$,
and let $s(n) = (\mathcal{M}_2(n), \mathcal{M}_2(2n + \mathcal{M}_2(n)))$. For every $n \ge 0$,
writing $s(n) = (x, y)$, we have $s(4n) = (y, x \oplus y)$, $s(4n+1) = (y \oplus 1, x \oplus y)$,
$s(4n+2) = (y \oplus 1, x \oplus y \oplus 1)$ and $s(4n+3) = (y, x \oplus y \oplus 1)$.
Moreover, $\mathcal{M}_2$ is $4$-automatic, and it is computed by a four-state automaton: there
are maps $\delta : \{0, 1, 2, 3\} \times \{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ and
$\tau : \{0, 1, 2, 3\} \to \{0, 1\}$ such that for every $n$, $\mathcal{M}_2(n) = \tau(q)$, where
$q$ is the state reached from the state $0$ by reading the base-$4$ digits of $n$ with $\delta$,
most significant digit first (for $n = 0$ no digit is read, so $q = 0$).

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Theorem 20 (`jis-2026-26.4.1-thm-20`).
