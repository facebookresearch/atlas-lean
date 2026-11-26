# Diagonal classes of size at most three

Let $\alpha$ be a partition of $n \ge 1$, let
$d = \delta(\alpha)$ be its diagonal sequence, written without its trailing zeros, and let
$[\alpha]$ be the set of partitions of $n$ with diagonal sequence $d$, each written by its parts
in decreasing order. Here $v^{(r)}$ means $r$ copies of $v$, and a run $a, a - 1, \dots, b$ with
$a < b$ is empty.
(1) If $|[\alpha]| = 1$, then there is $q \ge 1$ with $n = \binom{q+1}{2}$,
$d = (1, 2, \dots, q)$ and $[\alpha] = \{(q, q - 1, \dots, 1)\}$.
(2) If $|[\alpha]| = 2$, then either there are $q \ge 1$ and $k \ge 2$ with
$n = \binom{q+1}{2} + k$, $d = (1, 2, \dots, q, 1^{(k)})$ and
$[\alpha] = \{(q + k, q - 1, \dots, 1), (q, q - 1, \dots, 1, 1^{(k)})\}$, or $n = 2$,
$d = (1, 1)$ and $[\alpha] = \{(2), (1, 1)\}$.
(3) If $|[\alpha]| = 3$, then either there are $q \ge 2$ and $k \ge 2$ with
$n = \binom{q+1}{2} + 2k$, $d = (1, 2, \dots, q, 2^{(k)})$ and $[\alpha] = \{(q + k, q - 1 + k,
q - 2, \dots, 1), (q, q - 1, \dots, 3, 2^{(k+1)}, 1), (q + k, q - 1, \dots, 2, 1^{(k+1)})\}$, or
$d = (1, 2, 1)$ and $[\alpha] = \{(3, 1), (2, 2), (2, 1, 1)\}$, or $d = (1, 2, 2)$ and
$[\alpha] = \{(3, 2), (3, 1, 1), (2, 2, 1)\}$.

Part (4) of the corollary, on classes of size $4$, is false as printed and is not included.

## Sources

- Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*, INTEGERS 25 (2025), Article A60, Corollary 7 (1)–(3).
