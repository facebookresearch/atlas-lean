# Robust counterpart of a linear objective under ellipsoidal uncertainty

Let $E$ and $U$ be real Hilbert spaces, $x, c^\star \in E$, $t \in \mathbb{R}$ and $P \colon U \to E$ a continuous linear map. Then

$$
\langle c^\star + P u, x\rangle \le t \ \text{ for every } \|u\| \le 1 \iff \langle c^\star, x\rangle + \|P^\dagger x\| \le t .
$$

Minimizing the worst-case objective over an ellipsoid of cost vectors is thus minimizing $t$ under one conic quadratic constraint, the objective part of the robust counterpart (RLP).

## Sources

- A. Ben-Tal and A. Nemirovski, *Lectures on Modern Convex Optimization*, lecture notes (2020–2023); author PDF at <https://www2.isye.gatech.edu/~nemirovs/LMCOLN2023Spring.pdf>, Section 2.4.1, the objective part of (RLP).
