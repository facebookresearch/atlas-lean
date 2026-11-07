# Moves of the Accelerated Zeckendorf Game

Index the Fibonacci numbers as $F_1 = 1$,
$F_2 = 2$ and $F_{i+1} = F_i + F_{i-1}$, and call a finitely supported function
$s : \mathbb{N} \to \mathbb{N}$ a state, $s(i)$ being the number of copies of $F_i$. A move
takes a state $s$ to a state $t$ if for some multiplicity $m > 0$ one of the following holds:
the move $m \cdot C_i$ with $i \ge 2$, where $s(i-1) \ge m$, $s(i) \ge m$ and $t$ is
obtained from $s$ by removing $m$ copies each of $F_{i-1}$ and $F_i$ and adding $m$ copies
of $F_{i+1}$; the move $m \cdot C_1$, where $s(1) \ge 2m$ and $t$ is obtained by replacing
$2m$ copies of $F_1$ by $m$ copies of $F_2$; the move $m \cdot S_2$, where $s(2) \ge 2m$ and
$t$ is obtained by replacing $2m$ copies of $F_2$ by $m$ copies each of $F_1$ and $F_3$; or
the move $m \cdot S_i$ with $i \ge 3$, where $s(i) \ge 2m$ and $t$ is obtained by replacing
$2m$ copies of $F_i$ by $m$ copies each of $F_{i-2}$ and $F_{i+1}$.

## Sources

- Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1, Article milleretal04072023, Definition 1.2.
