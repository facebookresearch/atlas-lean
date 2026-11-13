# Fibonacci arch tops

Index the Fibonacci numbers as in the source, $F_0 = F_1 = 1$ and
$F_{j+2} = F_{j+1} + F_j$. Write $a/b$ for the position $(a, b)$ of Euclid, and call $a/(a+b)$
its son and $(a+b)/b$ its daughter. Let $n \ge 1$ and $k \ge 0$ be integers, and let
$X = (F_{2n+1} + kF_{2n-1})/(F_{2n+1} + (k-1)F_{2n-1})$ and
$Y = (F_{2n} + kF_{2n-2})/(F_{2n} + (k+1)F_{2n-2})$. Then $X$ is a P-position of Euclid, and so
are its son's daughter $(3F_{2n+1} + (3k-1)F_{2n-1})/(2F_{2n+1} + (2k-1)F_{2n-1})$ and its
daughter's son $(2F_{2n+1} + (2k-1)F_{2n-1})/(3F_{2n+1} + (3k-2)F_{2n-1})$. Likewise $Y$ is a
P-position of Euclid, and so are its son's daughter
$(3F_{2n} + (3k+1)F_{2n-2})/(2F_{2n} + (2k+1)F_{2n-2})$ and its daughter's son
$(2F_{2n} + (2k+1)F_{2n-2})/(3F_{2n} + (3k+2)F_{2n-2})$.

## Sources

- Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 5.3.
