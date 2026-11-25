# Minimum of a linear form over the unit ball

For $c \in \mathbb{R}$ and $v$ in a real inner product space,

$$
c + \langle u, v\rangle \ge 0 \ \text{ for every } \|u\| \le 1 \iff \|v\| \le c ,
$$

because the minimum of $\langle u, v\rangle$ over the unit ball is $-\|v\|$, attained at $u = -v/\|v\|$ (Cauchy–Schwarz gives the other direction). This is the one computation behind the conic quadratic form of robust linear constraints under ellipsoidal uncertainty.

## Sources

- A. Ben-Tal and A. Nemirovski, *Lectures on Modern Convex Optimization*, lecture notes (2020–2023); author PDF at <https://www2.isye.gatech.edu/~nemirovs/LMCOLN2023Spring.pdf>, Section 2.4.1: $\min_{u^T u \le 1} u^T P^T (x; -1) = -\|P^T (x; -1)\|_2$.
