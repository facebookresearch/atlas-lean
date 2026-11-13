# Moving a Fibonacci number of pairs in the Accelerated Zeckendorf Game

Index the
Fibonacci numbers as $F_1 = 1$, $F_2 = 2$, $F_{j+1} = F_j + F_{j-1}$, extended by $F_0 = 1$ and
$F_{-1} = 0$. Let $p \ge 2$ and $i \ge 1$, and let $s$ be a state with $F_{i-1}$ copies of
$F_{p-1}$, $F_i$ copies of $F_p$ and no copy of $F_{p+1}$. Let $t$ be the state obtained from $s$
by replacing $F_{i-1}$ copies of each of $F_{p-1}$ and $F_p$ by $F_{i-1}$ copies of $F_{p+1}$.
Then passing from $s$ to $t$ is a move, and $t$ has no copy of $F_{p-1}$, $F_{i-2}$ copies of
$F_p$ and $F_{i-1}$ copies of $F_{p+1}$.

## Sources

- Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1, Article milleretal04072023, Lemma 2.2.
