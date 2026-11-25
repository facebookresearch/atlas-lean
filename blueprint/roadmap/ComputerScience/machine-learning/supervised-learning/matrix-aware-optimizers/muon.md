# Muon optimizer

Muon (Jordan et al., 2024, as cited by the papers below) updates a weight matrix
$W \in \mathbb{R}^{m \times n}$ of a neural network layer as follows. Let $\lambda > 0$ be the
learning rate, $\beta \in [0, 1)$ the momentum coefficient, $G_t$ the (stochastic) gradient of the
loss with respect to $W$ at step $t$, and $M_0 = 0$. Then

$$M_t = \beta M_{t-1} + (1 - \beta) G_t, \qquad W_{t+1} = W_t - \lambda \, P(M_t),$$

where $P(M) = U_r V_r^{\mathsf{T}}$ is the canonical polar factor of $M$, built from a compact
singular value decomposition $M = U_r \Sigma_r V_r^{\mathsf{T}}$, and $P(0) = 0$.

- Momentum convention. Pethick et al. write the momentum as $G_k = g_k + \beta G_{k-1}$. With the
  same start, the two momenta differ by the positive factor $1 - \beta$, and
  $P(c M) = P(M)$ for $c > 0$, so the update is the same.
- Direction. For $\rho > 0$, $-\rho P(M_t)$ minimizes $\langle M_t, T \rangle$ over the spectral-norm ball
  $\|T\|_2 \le \rho$, uniquely when $M_t$ has full rank: Muon steps along the linear minimization
  oracle of the spectral-norm ball. Steepest descent under the spectral norm, with sharpness $s > 0$
  (Bernstein and Newhouse's $\lambda$), takes for a single layer a step (the unique one when $G$ has full rank)
  $-(\|G\|_* / s) U V^{\mathsf{T}}$, where $\|G\|_*$ is the nuclear norm and $U V^{\mathsf{T}}$ is
  taken from a reduced singular value decomposition. Muon drops the factor $\|G\|_*$; with
  non-Nesterov momentum it is then exactly the unconstrained stochastic conditional gradient method
  (uSCG) of Pethick et al. for the spectral-norm ball.
- Computation. Muon does not compute a singular value decomposition: it approximates $P(M_t)$ by a
  few steps, about five in bfloat16, of an odd polynomial iteration, so the update applied is that
  approximation. With Jordan's coefficients the exact iteration does not converge to $P(M_t)$ when $M_t \ne 0$.
  Amsel et al. propose Polar Express, which changes the polynomial at each step, and state a
  super-exponential convergence rate for it (their Theorem 3.3).
- Scope of use. Per-layer scale factors are a convention: Pethick et al. use $\sqrt{d_{out}/d_{in}}$
  for a $d_{out} \times d_{in}$ layer measured in the RMS-to-RMS operator norm, and other
  implementations scale differently. Muon is usually applied to hidden layers only, with Adam(W) or
  SGD for the first and last layers.

This page describes the update only. It makes no claim about the convergence, speed or final loss of
training with Muon; the convergence rates that Pethick et al. prove rest on their stated assumptions
and an exact oracle.

## Informally uses

- [Canonical polar factor of a rectangular matrix](../../../../LinearAlgebra/matrix-decompositions/polar-decomposition/polar-decomposition-theorem/rectangular-polar-factor.md):
  mathematical prerequisite, the update direction $P(M_t)$.
- [Properties of the canonical polar factor](../../../../LinearAlgebra/matrix-decompositions/polar-decomposition/polar-decomposition-theorem/canonical-polar-factor-properties.md):
  mathematical prerequisite, the invariance of $P(M_t)$ under positive scaling.
- [Duality of the spectral and nuclear norms](../../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/duality-of-the-spectral-and-nuclear-norms/spectral-norm-dual-nuclear-norm.md):
  mathematical prerequisite, which identifies $-\rho P(M_t)$ as the minimizer of a linear function
  over the spectral-norm ball.

## Background

- [Odd polynomial iterations for the polar factor](../../../../LinearAlgebra/matrix-decompositions/polar-decomposition/odd-polynomial-iterations-for-the-polar-factor/odd-polynomial-polar-iterations.md):
  computational prerequisite, how $P(M_t)$ is approximated in practice, and why a finite run is only
  an approximation.

## Sources

- N. Amsel, D. Persson, C. Musco and R. M. Gower, "The Polar Express: Optimal Matrix Sign Methods and Their Application to the Muon Algorithm", ICLR 2026, arXiv:2505.16932 (version 5), Section 1.1 (the update rule), Section 1.2 (Newton–Schulz, Jordan's and You's methods), Sections 3.4–3.5 with Algorithm 1, and Theorem 3.3.
- J. Bernstein and L. Newhouse, "Old Optimizer, New Norm: An Anthology", arXiv:2409.20325 (version 2), Proposition 5, equations (18)–(19), and Table 1.
- T. Pethick, W. Xie, K. Antonakopoulos, Z. Zhu, A. Silveti-Falls and V. Cevher, "Training Deep Learning Models with Norm-Constrained LMOs", ICML 2025, arXiv:2502.07529 (version 2), Section 4 (the "Muon" paragraph), Table 1 and its footnote, and Tables 2–3 (scale factors).
