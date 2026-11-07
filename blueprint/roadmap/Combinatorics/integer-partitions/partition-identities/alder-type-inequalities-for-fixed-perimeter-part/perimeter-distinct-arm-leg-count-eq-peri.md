# Refined equality of distinct-part and residue counts

Let $d$, $a$, $m$ and $k$ be natural
numbers with $d \ge 1$, $1 \le a \le d + 1$, $m \ge 1$ and $k \ge 1$. Write $h_d^{(a)}(m, k)$ for
the number of partitions into $d$-distinct parts, all at least $a$, with largest part $m$ and $k$
parts, and $f_d^{(a)}(m, k)$ for the number of partitions into parts congruent to $a$ modulo
$d + 1$ with largest part $m$ and $k$ parts. Then
$h_d^{(a)}(m, k) = f_d^{(a)}(a + (d + 1)(k - 1), j)$, where $j = \max(m + 1 - a - d(k - 1), 0)$.

In the source the second argument is $m + 1 - a - d(k - 1)$; it is replaced by $0$ when it is not
positive, and then both sides vanish.

## Sources

- Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102, Theorem 1.
