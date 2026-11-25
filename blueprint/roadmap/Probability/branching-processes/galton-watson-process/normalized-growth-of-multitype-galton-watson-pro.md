# Normalized growth of supercritical multitype Galton–Watson processes

Let $K\ge1$ types be given and let $(Z_n)_{n\ge0}$ be a [multitype Galton–Watson process](multitype-galton-watson-processes.md) with row vectors $Z_n\in\mathbb N^K$, so that $\mathbb E[Z_{n+1}\mid Z_0,\ldots,Z_n]=Z_nM$ for the mean matrix $M=(M_{ij})$. Assume:

- every offspring law has finite second moments;
- $M$ is primitive, with Perron root $\rho>1$, and by the [Perron–Frobenius theorem for primitive nonnegative matrices](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md) let $u>0$ and $v>0$ satisfy $Mu=\rho u$, $v^{\mathsf T}M=\rho v^{\mathsf T}$ and $v\cdot u=1$;
- the process is nonsingular, that is, it is not the case that every individual has exactly one child almost surely;
- the initial population is deterministic, $Z_0=z_0\in\mathbb N^K\setminus\{0\}$, or more generally $Z_0$ is independent of the offspring variables with $\mathbb E\|Z_0\|^2<\infty$.

Then

$$W_n=\frac{Z_n\cdot u}{\rho^n}$$

is a nonnegative martingale for the natural filtration that converges almost surely and in $L^2$ to a limit $W$, and

$$\frac{Z_n}{\rho^n}\longrightarrow W\,v\qquad\text{almost surely}.$$

For $K=1$ this is the [Galton–Watson martingale and its finite-variance limit](galton-watson-martingale-w-n-z-n-m-n.md) with $u=v=1$ and $\rho=m$.

## Depends on

- [Mean identity for multitype Galton–Watson processes](multitype-galton-watson-processes.md)
- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)

## Proof depends on

- [The Galton–Watson martingale and its finite-variance limit](galton-watson-martingale-w-n-z-n-m-n.md)

## Expansion

A full proof page must establish the following.

- The martingale property from $\mathbb E[Z_{n+1}\cdot u\mid\mathcal F_n]=Z_nMu=\rho\,Z_n\cdot u$, and integrability.
- $L^2$-boundedness of $W_n$ from the conditional variance recursion, using finite second moments, $\rho>1$ and the square-integrable start.
- The vector limit: decompose $Z_n$ along $v$ and the complementary $M$-invariant subspace, and use $\rho^{-n}M^n\to uv^{\mathsf T}$ together with a second-moment bound on the complementary component to get $Z_n/\rho^n-W_nv\to0$ almost surely.
- The reduction to one type.
- A guard showing that the hypothesis on $Z_0$ is needed for $L^2$ convergence: with one type, deterministic offspring number $2$ and a random $Z_0$ with $\mathbb EZ_0^2=\infty$, one has $W_n=Z_0$ for all $n$, which converges but is not in $L^2$.

## Sources

- K. B. Athreya and P. E. Ney, *Branching Processes*, Springer (1972), <https://link.springer.com/chapter/10.1007/978-3-642-65371-1_1>, multitype limit theorems (statement and proof).
