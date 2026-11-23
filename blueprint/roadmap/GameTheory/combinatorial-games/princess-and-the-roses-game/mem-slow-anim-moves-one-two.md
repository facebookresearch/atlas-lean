# Options in Princess and the Roses

Let $p$ and $q$ be positions of Slow$A$-Nim on $k$
stacks with $A = \{1, 2\}$, which is the Princess and the Roses game. Then $q$ is an option of
$p$ if and only if there are stacks $i \le j$ with $p_i \ge 1$ and $p_j \ge 1$ such that
$q_l = p_l - 1$ for $l \in \{i, j\}$ and $q_l = p_l$ for every other stack $l$; that is, $q$
removes one token from stack $i$ when $i = j$, and one token from each of stacks $i$ and $j$
otherwise.

## Sources

- Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*, INTEGERS 26 (2026), Article G4, Section 2.1.
