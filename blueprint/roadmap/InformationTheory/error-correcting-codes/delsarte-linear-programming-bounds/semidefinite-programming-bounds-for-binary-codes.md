# Schrijver: semidefinite programming bounds strengthen Delsarte's bound

There is a semidefinite program of size polynomial in $n$, based on the Terwilliger algebra of the Hamming scheme (triples of codewords), whose optimum $\mathrm{SDP}(n, d)$ satisfies $A(n, d) \le \mathrm{SDP}(n, d) \le \mathrm{LP}(n, d)$, with strict improvement for many small parameters (for instance new upper bounds on $A(n, d)$ for $n \le 28$).

## Proof sketch

Replace the distance distribution by the counts of codeword triples according to their three pairwise distances and common-zero patterns. Positive semidefiniteness of two matrices built from these counts, block-diagonalized by the representation theory of the Terwilliger algebra into polynomially many small blocks, gives valid constraints that imply Delsarte's inequalities.

## Depends on

- [Delsarte's linear programming bound](delsarte-linear-programming-bound.md)

## Sources

- Alexander Schrijver, "New code upper bounds from the Terwilliger algebra and semidefinite programming", IEEE Transactions on Information Theory 51(8) (2005).
