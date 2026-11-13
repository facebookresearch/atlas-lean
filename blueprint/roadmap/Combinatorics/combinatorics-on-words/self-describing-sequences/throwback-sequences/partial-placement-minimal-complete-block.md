# Minimal complete blocks of partial placements match configurations

Let
$X = (x_0, x_1, \dots)$ be a strictly increasing sequence of positive integers, let $\tau$ be
the throwback, let $n \ge 0$, and write $P_n(X)_z$ for the entry, possibly empty, of the
partial placement sequence $P_n(X)$ at position $z \in \mathbb{Z}$. The minimal complete block
at $z$ is the word $P_n(X)_z, P_n(X)_{z+1}, \dots, P_n(X)_{z+L-1}$, empty positions included,
where $L$ is the least length for which these positions contain every $x_i$ with $i \le n$
($L = 0$ if there is no such length). Then for all natural numbers $k$ and $l$, the minimal
complete blocks at $k$ and at $l$ are equal if and only if each of $x_0, \dots, x_n$ occupies
the same positions in $\tau^k(X)$ as in $\tau^l(X)$. Moreover, for every $z \in \mathbb{Z}$ the
minimal complete block at $z$ equals the minimal complete block at some natural number $k$.
So minimal complete blocks of $P_n(X)$ correspond bijectively to the configurations of
$x_0, \dots, x_n$ in the sequences $\tau^k(X)$ with $k \ge 0$.

## Sources

- Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*, Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 8 (`jis-2025-25.5.1-lem-8`).
