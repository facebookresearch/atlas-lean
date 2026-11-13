# Mallows levels

Fractions $n/m$ are written as pairs $(n, m)$ of natural numbers. Start
from the list $\langle 0/1, 1/1\rangle$ and refine it repeatedly, each refinement step inserting
between every two adjacent entries the pair of fractions given by Mallows' insertion rule. For
$i \ge 1$, $MT_i$ is the list of the fractions inserted at the $i$-th step: the fractions that
Mallows' rule inserts between adjacent entries of the list obtained after $i - 1$ steps, taken
from left to right, two for each adjacent pair.

After $k$ steps the list has $3^k + 1$ entries, so $MT_i$ has $2 \cdot 3^{i-1}$ entries.

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Section 2.3.
