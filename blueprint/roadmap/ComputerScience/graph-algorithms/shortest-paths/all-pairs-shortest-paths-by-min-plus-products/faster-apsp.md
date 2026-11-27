# FASTER-APSP

Let $W$ be an $n \times n$ matrix over a type with addition, multiplication
and zero. FASTER-APSP copies $W$ into a matrix $L$ and sets $r = 1$. While $r < n - 1$, it fills
a new $n \times n$ matrix $M$ with zeros, sets each entry to
$M_{ij} = 0 + L_{i0} L_{0j} + \dots + L_{i,n-1} L_{n-1,j}$ (adding the terms from left to right),
copies $M$ into $L$ and doubles $r$. It returns the final $L$. The run also records three counts:
one assignment for each matrix cell copied or filled with zero, and one scalar addition and one
scalar multiplication for each term added to an entry of $M$.
