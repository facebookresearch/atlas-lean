# Each term eventually settles or leads infinitely often

Let $X = (x_0, x_1, \dots)$ be a
sequence of positive integers, with positions numbered from $0$, the leader being at position
$0$. Track the terms of $X$ by their original indices: start from the arrangement
$(0, 1, 2, \dots)$ and apply the throwback repeatedly, where the leader, with original index
$i$, moves to position $x_i$. Then for every index $j$, either there are a position $p > 0$ and
a number $N$ such that the term with original index $j$ is at position $p$ after $k$ throwbacks
for every $k \ge N$, or there are infinitely many $k$ such that this term is the leader after
$k$ throwbacks.

## Sources

- Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*, Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 1 (`jis-2025-25.5.1-lem-1`).
