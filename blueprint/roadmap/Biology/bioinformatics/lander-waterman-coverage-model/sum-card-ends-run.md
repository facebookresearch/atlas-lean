# Exact count of run ends

Let $G$, $N$ and $V$ be natural numbers with $V + 1 \le G$. The number of pairs of a position
$p \in \{0, \dots, G-1\}$ and a start tuple $(s_1, \dots, s_N) \in \{0, \dots, G-1\}^N$ such that
$p$ is a [run end](ends-run.md) for the window $V$ is

$$G \bigl((G - V)^N - (G - V - 1)^N\bigr),$$

that is, summed over the positions $p$, the number of start tuples with a run end at $p$. For
$N = 0$ both sides are $0$.
