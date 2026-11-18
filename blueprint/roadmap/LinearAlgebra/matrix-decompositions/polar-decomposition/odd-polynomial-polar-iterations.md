# Odd polynomial iterations for the polar factor

Let $X$ be a real $m \times n$ matrix with compact singular value decomposition
$X = U_r \Sigma_r V_r^{\mathsf{T}}$, $r = \operatorname{rank} X$, and canonical polar factor
$P(X) = U_r V_r^{\mathsf{T}}$ ($P(0) = 0$). For an odd polynomial
$p(x) = \sum_{j = 0}^{q} a_j x^{2j + 1}$ define

$$p(X) = \sum_{j = 0}^{q} a_j X (X^{\mathsf{T}} X)^{j},$$

which uses only sums and products of $X$ and $X^{\mathsf{T}}$.

1. Calculus. $p(X) = U_r \, p(\Sigma_r) \, V_r^{\mathsf{T}}$, where $p(\Sigma_r)$ is diagonal with
   entries $p(\sigma_i)$; directions with singular value $0$ stay $0$; and for odd polynomials $p$
   and $p'$, $(p \circ p')(X) = p(p'(X))$. The identity holds even if some $p(\sigma_i) \le 0$, but
   then $U_r \, p(\Sigma_r) \, V_r^{\mathsf{T}}$ is no longer a singular value decomposition. Even
   polynomials of the singular values of a rectangular $X$ cannot be formed this way.
2. Cubic Newton–Schulz iteration. Let $X_{t+1} = \tfrac{3}{2} X_t - \tfrac{1}{2} X_t X_t^{\mathsf{T}} X_t$,
   the iteration of $f(x) = (3x - x^3)/2$. If every positive singular value of $X_0$ lies in
   $(0, \sqrt{3})$, then $X_t \to P(X_0)$. This condition is sufficient, not necessary.
3. Normalization. If $G = 0$, then $P(G) = 0$ and every iterate from $X_0 = 0$ is $0$. If $G \ne 0$,
   $X_0 = G / \|G\|_F$ has all its positive singular values in $(0, 1]$, because
   $\sigma_1(G) \le \|G\|_F$, and $P(X_0) = P(G)$; so the iteration from $X_0$ converges to $P(G)$.
4. Worst case. For a fixed odd polynomial $p$, integers $m, n \ge 1$ and $0 < \ell \le u$,
   $\max \{ \|P(M) - p(M)\|_2 : M \in \mathbb{R}^{m \times n},\ \sigma(M) \subset [\ell, u] \} = \max_{x \in [\ell, u]} |1 - p(x)|$,
   where $\sigma(M)$ is the set of all $\min(m, n)$ singular values of $M$.

Proof: $X^{\mathsf{T}} X = V_r \Sigma_r^2 V_r^{\mathsf{T}}$, so
$X (X^{\mathsf{T}} X)^j = U_r \Sigma_r^{2j + 1} V_r^{\mathsf{T}}$; the same computation applies to
$U_r D V_r^{\mathsf{T}}$ for any real diagonal $D$, which gives the composition rule. For item 2, each
positive singular value moves by $x \mapsto f(x)$. On $(0, 1)$, $f(x) - x = x (1 - x^2)/2 > 0$ and
$1 - f(x) = (1 - x)^2 (2 + x)/2 > 0$, so the values increase to the fixed point $1$; on
$[1, \sqrt{3})$, $f(x) \in (0, 1]$. Hence $X_t = U_r f^{t}(\Sigma_r) V_r^{\mathsf{T}} \to P(X_0)$.
Item 3 uses $\|G\|_F^2 = \sum_i \sigma_i^2$ and the scale invariance of $P$. In item 4 every such $M$
has full rank, $P(M) - p(M) = U_k (I - p(\Sigma_k)) V_k^{\mathsf{T}}$ for a thin decomposition, and
every $x \in [\ell, u]$ occurs as a singular value.

The convergence interval of item 2 cannot be stated as an "if and only if" (derived here): the point
$x^* = \sqrt[3]{2 + \sqrt{3}} + \sqrt[3]{2 - \sqrt{3}} \approx 2.1958 > \sqrt{3}$ is a root of
$x^3 - 3x - 4$, so $f(x^*) = -2$ and $f(-2) = 1$, and the iteration from the $1 \times 1$ matrix
$(x^*)$ reaches $P = 1$ in two steps, while from $(1.8)$ it converges to $-1 \ne P$. Beyond
$\sqrt{3}$ the set of starting values that converge to $1$ is irregular.

Finite steps. After $T$ steps of an iteration with a fixed odd $p$,
$X_T = U_r \, p^{\circ T}(\Sigma_r) \, V_r^{\mathsf{T}}$ and
$\|P(X_0) - X_T\|_2 = \max_{i \le r} |1 - p^{\circ T}(\sigma_i)|$ when $r \ge 1$, so a finite run is an approximation; when $r = 0$, that is $X_0 = 0$, both $P(X_0)$ and $X_T$ are $0$ and the error is $0$. This singular-value-wise identity holds in exact arithmetic only. In the Muon
optimizer the iteration runs for about five steps in bfloat16, and the normalization and safety
constants differ between implementations; they are implementation details, not part of the
mathematics above.

Coefficient choices matter, and statements about convergence are specific to the coefficients:

- The classical quintic $p(x) = (15x - 10x^3 + 3x^5)/8$ has $p(1) = 1$,
  $p'(x) = 15 (1 - x^2)^2 / 8 \ge 0$ and $p(x) - x = x (1 - x^2)(7 - 3x^2)/8 > 0$ on $(0, 1)$, so it
  converges to $P(X_0)$ whenever the positive singular values of $X_0$ lie in $(0, 1]$ (Amsel et al.
  state its convergence; this monotonicity argument is derived here).
- Jordan's quintic $p(x) = 3.4445x - 4.7750x^3 + 2.0315x^5$, as printed by Amsel et al., has
  $p(1) = 0.701 \ne 1$. If the iterates converged to $P(M)$ for some $M \ne 0$, a positive singular
  value would tend to $1$ and, by continuity, its image would tend to $p(1)$, so $p(1) = 1$. Hence the
  exact iteration with these coefficients converges to $P(M)$ for no nonzero $M$ (derived here).
  Amsel et al. report that its error plateaus near $0.3$. This says nothing about whether training with Muon converges.
- You's scheme applies six different polynomials, one per step, so it is defined for six steps only;
  Amsel et al., citing Cesista et al., report that it does not reach $P(M)$.

## Informally uses

- [Real singular value decomposition](../singular-value-decomposition/real-singular-value-decomposition.md):
  mathematical prerequisite, the decomposition through which $p(X)$ acts on singular values.
- [Canonical polar factor of a rectangular matrix](rectangular-polar-factor.md): mathematical
  prerequisite, the limit $P(X_0)$ of the iteration and its scale invariance.
- [Squared Frobenius norm as the sum of squared singular values](../singular-value-decomposition/sum-sq-singular-values-eq-sum-sq-norm-of.md):
  mathematical prerequisite, the bound $\sigma_1(G) \le \|G\|_F$ that justifies the normalization
  $X_0 = G / \|G\|_F$.

## Sources

- N. Amsel, D. Persson, C. Musco and R. M. Gower, "The Polar Express: Optimal Matrix Sign Methods and Their Application to the Muon Algorithm", ICLR 2026, arXiv:2505.16932 (version 5), Section 1.2 and equation (2) (Newton–Schulz, Jordan's and You's methods), the Notation paragraph at the end of Section 1 and its footnote in Section 2, equations (3)–(6), Appendix E (the worst-case reduction), and Sections 3.4–3.5 with Algorithm 1 (finite precision).
- J. Bernstein and L. Newhouse, "Old Optimizer, New Norm: An Anthology", arXiv:2409.20325 (version 2), Appendix A, equations (36)–(37) (Newton–Schulz and its convergence interval).
- N. J. Higham, Functions of Matrices: Theory and Computation, SIAM (2008), Chapter 8 (Newton–Schulz iteration for the polar factor).
