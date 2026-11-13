# Offset form of Sury's identity for a second-order recurrence

Let $c_1, c_2$ be rational
numbers with $c_2 \neq 0$, and let $(X_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers
with $X_{n+2} = c_1 X_{n+1} + c_2 X_n$ for all integers $n$. Let $k$ be an integer with
$X_k \neq 0$ and $X_{k-1} \neq 0$. Then for every natural number $n$,

$$X_0 X_{n+2} - X_1 X_{n+1} = \frac{X_0 X_2 - X_1^2}{X_k}
\sum_{i=0}^{n} \left(\frac{-c_2 X_{k-1}}{X_k}\right)^{n-i} X_{i+k}.$$

The offset $k$ may be negative; requiring the recurrence at every integer index encodes the
paper's backward extension of the sequence, which uses $c_2 \neq 0$.

## Sources

- Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 2.
