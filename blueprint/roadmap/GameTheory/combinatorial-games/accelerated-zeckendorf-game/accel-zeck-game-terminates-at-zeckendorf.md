# The Accelerated Zeckendorf Game terminates at the Zeckendorf decomposition

Index the
Fibonacci numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Let $n$ be a natural
number, let $Z(n)$ be the number of terms of the Zeckendorf decomposition of $n$, and let $IZ(n)$
be the sum of the indices $k$ of its terms $F_k$. Then there is no infinite sequence of moves
starting from $n$ copies of $F_1$. Moreover, every complete Accelerated Zeckendorf Game on $n$
(a sequence of moves from $n$ copies of $F_1$ to a state from which no move is possible) ends at
the state with one copy of each term of the Zeckendorf decomposition of $n$, and its number $L$
of moves satisfies

$$L \le \frac{3 + \sqrt 5}{2} n - IZ(n) - \frac{1 + \sqrt 5}{2} Z(n).$$

## Sources

- Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1, Article milleretal04072023, Theorem 1.3.
