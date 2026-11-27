# Convexity of the Floquet eigenvalue in death and birth rates

**Model.** Consider a cell population structured by phase $i\in\{1,\dots,I\}$ and age $x\ge0$ within the phase. With time-periodic coefficients it follows the linear renewal system

$$\partial_tn_i+\partial_xn_i+d_i(t,x)\,n_i=0,\qquad n_i(t,0)=\sum_j\int_0^\infty B_{j\to i}(t,x)\,n_j(t,x)\,dx,$$

where the death rates $d_i\ge0$ and birth or transition rates $B_{j\to i}\ge0$ are $T$-periodic in $t$. The cell-division-cycle model with transition rates $K_{i\to i+1}$ and doubling at mitosis is a special case. The long-run growth of the population is governed by the dominant (Floquet) eigenvalue $\lambda_F$: there are a nonnegative $T$-periodic eigenfunction and a positive periodic adjoint eigenfunction with growth $e^{\lambda_Ft}$. When these do not exist, $\lambda_F$ is defined as the infimum of the $\mu$ that admit a positive periodic adjoint sub-eigenfunction (a Collatz–Wielandt characterization).

**Theorem.** $\lambda_F$ is convex in the death rates and geometrically convex in the birth rates. Take two sets of $T$-periodic coefficients $(B^1,d^1)$ and $(B^2,d^2)$ with eigenvalues $\lambda_F^1$ and $\lambda_F^2$. For $\theta\in[0,1]$ define

$$d_i^\theta=\theta d_i^1+(1-\theta)d_i^2,\qquad B_{j\to i}^\theta=(B_{j\to i}^1)^\theta(B_{j\to i}^2)^{1-\theta}.$$

Then the eigenvalue $\lambda_F^\theta$ of $(B^\theta,d^\theta)$ satisfies

$$\lambda_F^\theta\le\theta\lambda_F^1+(1-\theta)\lambda_F^2 .$$

**Consequences.**

- Replace death rates by their time averages and birth rates by their geometric time averages $\exp\bigl(T^{-1}\int_0^T\log B_{j\to i}\,dt\bigr)$, and call the resulting eigenvalue $\lambda_g$. The inequality $\lambda_g\le\lambda_F$ can be recovered from the theorem by Jensen's inequality.
- In particular, if the birth rates are time-independent, the Perron eigenvalue $\lambda_P$ of the time-averaged system satisfies $\lambda_P\le\lambda_F$. Periodic modulation of death rates alone never slows population growth compared with constant death at the same mean.

## Expansion

The proof is a continuous analogue of Kingman's theorem that the log Perron root of a nonnegative matrix is convex in its diagonal entries and geometrically convex in its off-diagonal entries. Death acts locally (like a diagonal entry) and birth acts nonlocally through the boundary condition (like an off-diagonal entry). If $\phi^1,\phi^2>0$ are adjoint sub-eigenfunctions for $(\mu_1,B^1,d^1)$ and $(\mu_2,B^2,d^2)$, divide each inequality by $\phi^k$ and take the convex combination of the equations for $\log\phi^k$. The arithmetic–geometric mean inequality $\theta a+(1-\theta)b\ge a^\theta b^{1-\theta}$ applied to the boundary terms then shows that $\phi^\theta=(\phi^1)^\theta(\phi^2)^{1-\theta}$ is a sub-eigenfunction for $(\theta\mu_1+(1-\theta)\mu_2,B^\theta,d^\theta)$. Letting $\mu_k\downarrow\lambda_F^k$ concludes.

## Sources

- Jean Clairambault, Stéphane Gaubert, Thomas Lepoutre, "Circadian rhythm and cell population growth", arXiv:1006.3459 (2010), Section 3 (age-structured renewal system, averaged-coefficient comparisons), Theorem 1 and the section "Proof of the convexity result", <https://doi.org/10.48550/arXiv.1006.3459>.
