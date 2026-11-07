# A four-state automaton computing $\mathcal{M}_2$

Let
$\delta : \{0, 1, 2, 3\} \times \{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ be the map for which the word
$\delta(q, 0)\,\delta(q, 1)\,\delta(q, 2)\,\delta(q, 3)$ is $0132$ for $q = 0$, $2310$ for $q = 1$,
$3201$ for $q = 2$ and $1023$ for $q = 3$. For every natural number $n$, the meta-automatic
sequence $\mathcal{M}_2$, read as taking values in $\{0, 1\}$, satisfies
$\mathcal{M}_2(n) = q \bmod 2$, where $q$ is the state reached from the state $0$ by reading the
base-$4$ digits of $n$ with $\delta$, most significant digit first (for $n = 0$ no digit is read,
so $q = 0$).

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Theorem 22 (`jis-2026-26.4.1-thm-22`).
