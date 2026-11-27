# Positive left Perron vector of an irreducible matrix

Let $A$ be a real square matrix indexed by a nonempty finite set $S$ that is irreducible: its entries are nonnegative and for all $i, j \in S$ there is a path $i = i_0, i_1, \dots, i_k = j$ with $k \ge 1$ and $A_{i_{t-1}i_t} > 0$ for every $t$. Then $A^{\mathsf T}$ is irreducible, and with $r > 0$ the Perron root of $A$ (the largest absolute value of an eigenvalue) there is a vector $w$ with $w_i > 0$ for every $i$ and $w^{\mathsf T}A = r\,w^{\mathsf T}$.

Proof. Reversing a path with positive entries of $A$ from $i$ to $j$ gives a path with positive entries of $A^{\mathsf T}$ from $j$ to $i$, so $A^{\mathsf T}$ is irreducible. The Perron–Frobenius theorem for $A^{\mathsf T}$ gives $r' > 0$ and $w$ with positive entries and $A^{\mathsf T}w = r'w$, that is $w^{\mathsf T}A = r'w^{\mathsf T}$, and every eigenvalue of $A^{\mathsf T}$ has absolute value at most $r'$. Since $A$ and $A^{\mathsf T}$ have the same characteristic polynomial, $r$ is an eigenvalue of $A^{\mathsf T}$ and $r'$ one of $A$, so $r \le r'$ and $r' \le r$.

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](perron-frobenius.md): applied to the transpose.

## Expansion

- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
