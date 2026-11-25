# Real and complex stability of a real linear system agree

Let $A \in \mathbb{R}^{n \times n}$, and let $A_{\mathbb{C}}$ be the same matrix acting on $\mathbb{C}^n$. Use the Euclidean norms on $\mathbb{R}^n$ and $\mathbb{C}^n$ and the induced operator norms.

1. **Norms.** For every real matrix $M \in \mathbb{R}^{n \times n}$, the operator norm of $M$ on $\mathbb{C}^n$ equals its operator norm on $\mathbb{R}^n$. In particular $\|e^{tA_{\mathbb{C}}}\| = \|e^{tA}\|$ for all $t$, and $\|A_{\mathbb{C}}^k\| = \|A^k\|$ for all $k$.
2. **Continuous time.** The following are equivalent: every real solution of $\dot x = Ax$ tends to $0$; every complex solution of $\dot z = A_{\mathbb{C}}z$ tends to $0$; there are $c, \lambda > 0$ with $\|e^{tA}\| \le ce^{-\lambda t}$ for $t \ge 0$; every eigenvalue of $A$ (a complex number) has negative real part.
3. **Discrete time.** The following are equivalent: every real solution of $x_{k+1} = Ax_k$ tends to $0$; every complex solution tends to $0$; there are $c > 0$ and $\rho < 1$ with $\|A^k\| \le c\rho^k$; every eigenvalue of $A$ has modulus less than $1$.

So the real system and its complexification are stable together, and the eigenvalue tests may be read in either; nonreal eigenvalues of a real matrix come in conjugate pairs and contribute oscillating real solutions.

**Proof.** For part 1, write $z = x + iy$ with $x, y \in \mathbb{R}^n$; then $Mz = Mx + iMy$ and $\|Mz\|^2 = \|Mx\|^2 + \|My\|^2 \le \|M\|^2_{\mathbb{R}}(\|x\|^2 + \|y\|^2) = \|M\|^2_{\mathbb{R}}\|z\|^2$, and real vectors show the reverse inequality. The exponential and the powers of a real matrix are real, which gives the two identities. In part 2, complex solutions are $z(t) = e^{tA_{\mathbb{C}}}z_0 = e^{tA}x_0 + ie^{tA}y_0$, so real and complex convergence agree; the equivalence of convergence of all real solutions, the exponential bound and the condition on the complex eigenvalues is the stability theorem for linear differential equations, and part 1 transfers the bound between the real and the complex operator norm. Part 3 is the same argument with $A^k$ and the stability theorem for linear difference equations.

## Proof depends on

- [Exponential stability of linear differential equations](asymptotic-stability-linear-differential-equations.md): convergence, exponential bound and eigenvalues in the open left half-plane
- [Exponential stability of linear difference equations](asymptotic-stability-linear-difference-equations.md): convergence, geometric bound and eigenvalues in the open unit disk

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Appendix C, the remark that a complex linear system can be regarded as a real system on $\mathbb{R}^{2n}$, again linear (p. 487); Section 5.5 and Section 7.3, where asymptotic stability of linear systems is characterized by eigenvalues of $A$ in the complex half-plane or disk. The norm identity is proved on the page.
