# One node of the Chan-He recursion

At a node with three sets $P, Q, R$ and modulus $M$, call an element **light** if it is alone in its residue class modulo $M$ within its set. Place each light element of $P$ and $Q$ at the index of its residue in arrays of length $M$, and each light element of $R$ at the index of minus its residue in an array of length $2M$. Then $(P, Q, R)$ has a solution with all three elements light if and only if the resulting Convolution-3SUM instance, read with $X[i] + Y[j] = Z[i+j]$ after appropriate sign and offset conventions, has a solution; every remaining solution uses at least one heavy element and is a solution of one of three child nodes in which one set is replaced by its heavy elements.

## Proof sketch

If $p + q + r = 0$ then $p \bmod M + q \bmod M \equiv -r \pmod M$; lightness makes the residue determine the element, and the index sum distinguishes the two possible carries.

## Depends on

- [Convolution-3SUM](convolution-three-sum.md)
- [Choosing a hashing modulus with few heavy elements](chan-he-modulus-choice.md)

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
