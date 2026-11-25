# Kalman rank condition, dual form

Let $E$ be a finite-dimensional real inner product space, $U$ a real inner product space (not necessarily finite-dimensional), and $A : E \to E$, $B : U \to E$ bounded linear maps. The [Kalman subspace](kalman-subspace.md) of $(A, B)$ is all of $E$ if and only if the only vector $\eta \in E$ orthogonal to $A^k B v$ for every $k \in \mathbb{N}$ and every $v \in U$ is $\eta = 0$. Powers $k \ge \dim E$ add nothing to the Kalman subspace, by the Cayley–Hamilton theorem. Finite dimension of $E$ is needed: on real $\ell^2$, with $A$ the unilateral shift and $B u = u e_0$ for $u \in \mathbb{R}$, the vectors $A^k B u$ span a dense proper subspace, so only $\eta = 0$ is orthogonal to all of them.

## Background

- [Kalman subspace](kalman-subspace.md): its orthogonal complement is $\{0\}$ exactly when it is the whole space.
