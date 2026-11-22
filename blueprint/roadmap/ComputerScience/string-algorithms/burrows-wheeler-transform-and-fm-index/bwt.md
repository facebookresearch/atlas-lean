# Burrows–Wheeler transform

Let $t = t_0 \cdots t_{n-1}$ be a text over a linearly ordered alphabet $\alpha$, and let
$t\bot = t_0 \cdots t_{n-1} \bot$ be $t$ followed by a sentinel $\bot$ that is smaller than every
letter. The Burrows–Wheeler transform of $t$ is the list of length $n + 1$ whose entry at row
$r \le n$ is the last letter of row $r$ of the Burrows–Wheeler matrix, that is, of the rotation of
$t\bot$ starting at position $R[r]$, where $R$ lists the positions $0, \dots, n$ sorted by their
rotations in lexicographic order.
