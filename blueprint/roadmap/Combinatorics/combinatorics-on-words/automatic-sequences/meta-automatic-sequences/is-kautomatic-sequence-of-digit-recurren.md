# Allouche–Shallit criterion for automatic sequences

Let $A$ be a finite set,
$U : \mathbb{N} \to A$ a sequence and $q \ge 2$ a natural number. Let $t, a, b, n_0$ be natural
numbers, let $P$ be the set of pairs $(i, j')$ of natural numbers with $i \le t$, $j' < q^i$ and
$(i, j') \ne (0, 0)$, and for each natural number $j$ let $f_j$ map families of elements of $A$
indexed by the disjoint union of $\{0, 1, \dots, a + b\}$ and $P$ to $A$. Suppose that for all
$n \ge n_0$ and $j < q^{t+1}$, $U(q^{t+1} n + j)$ is the value of $f_j$ at the family sending
$k \in \{0, \dots, a + b\}$ to $U(n + k - a)$ and $(i, j') \in P$ to $U(q^i n + j')$, where
$n + k - a$ is read as $0$ when it is negative. Then $U$ is $q$-automatic.

The arguments $U(n - a), \dots, U(n + b)$ are truncated only when $n < a$, which is harmless
since only large $n$ matter; the paper notes that the order of the arguments plays no role.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Theorem 2, quoting Allouche and Shallit (2012), Theorem 2.2 (`jis-2026-26.4.1-thm-2`).
