# The Fibonacci arches

Let $F_j$ be the Fibonacci numbers with $F_0 = F_1 = 1$ and
$F_{j+2} = F_{j+1} + F_j$. Call a pair $(a, b)$ of natural numbers a P-position when the Euclid
P-position test returns true at $(a, b)$, read it as the vertex $a/b$ of the Calkin–Wilf tree, and
let $s(a/b) = a/(a+b)$ be its son and $d(a/b) = (a+b)/b$ its daughter; write $s^k$ and $d^k$ for
the $k$-fold iterates. Let $n \ge 1$ and $k \ge 0$, and let $V = F_{2n-1}/F_{2n-2}$. Then $V$ is a
P-position, its son's daughter $d(s(V))$ is $F_{2n+1}/F_{2n}$, and its daughter's son $s(d(V))$
is $F_{2n}/(F_{2n} + F_{2n-2})$. The vertex $L = d(s^k((F_{2n+1} - F_{2n})/F_{2n}))$ is a
P-position whose numerator is $F_{2n+1} + kF_{2n-1}$ and whose denominator is
$F_{2n+1} + (k-1)F_{2n-1}$, and the vertex $R = s(d^k(F_{2n}/F_{2n-2}))$ is the P-position
$(F_{2n} + kF_{2n-2})/(F_{2n} + (k+1)F_{2n-2})$.

Here $L$ and $R$ are level $k$ (level $0$ the top) of the left and right branches of the arch
topped by $d(s(V))$ and $s(d(V))$.

## Sources

- Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 5.2.
