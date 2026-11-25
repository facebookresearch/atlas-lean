# Exact count of gaps of length at least $m$

Let $G$, $N$, $L$ and $m$ be natural numbers with $L > 0$, $m > 0$ and $L + m \le G$. The number
of pairs of a base $x \in \{0, \dots, G-1\}$ and a start tuple
$(s_1, \dots, s_N) \in \{0, \dots, G-1\}^N$ of reads of length $L$ such that $x$ is the
[last base of a gap of at least $m$ uncovered bases before coverage](gap-at-least.md) is

$$G \bigl((G - (L + m - 1))^N - (G - (L + m))^N\bigr),$$

that is, summed over the bases $x$, the number of start tuples with such a mark at $x$. For
$m = 1$ this counts the maximal uncovered runs followed by a covered base. For $N = 0$ both sides
are $0$.
