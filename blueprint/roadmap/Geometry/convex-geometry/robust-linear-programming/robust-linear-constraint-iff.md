# Robust counterpart of a linear constraint under ellipsoidal uncertainty

Let $E$ and $U$ be real Hilbert spaces, $x, a^\star \in E$, $b^\star \in \mathbb{R}$, $A \colon U \to E$ a continuous linear map and $q \in U$. Let the data $(a, b)$ of the linear constraint $\langle a, x\rangle - b \ge 0$ run through the ellipsoid

$$
\{(a^\star + A u,\ b^\star + \langle q, u\rangle) : \|u\| \le 1\} .
$$

Then $x$ satisfies the constraint for every realization of the data if and only if

$$
\|A^\dagger x - q\| \le \langle a^\star, x\rangle - b^\star ,
$$

where $A^\dagger$ is the adjoint. A robust linear program with such "simple ellipsoidal" uncertainty, each constraint's data in its own ellipsoid, is therefore a conic quadratic program: robustness costs one second-order cone constraint per uncertain row. In the source's notation the perturbation $P u$ of $(a; b)$ has block rows $A$ and $q^T$, so that $P^T (x; -1) = A^T x - q$.

## Sources

- A. Ben-Tal and A. Nemirovski, *Lectures on Modern Convex Optimization*, lecture notes (2020–2023); author PDF at <https://www2.isye.gatech.edu/~nemirovs/LMCOLN2023Spring.pdf>, Section 2.4.1, the derivation of the constraints of (RLP).
