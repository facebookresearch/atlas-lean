# Ensemble collapse for continuous-time ensemble Kalman inversion

Let $X$ be a real Hilbert space, $Y$ a finite-dimensional real inner product space, $A : X \to Y$ bounded and linear, $\Gamma$ a positive invertible covariance on the
finite-dimensional data space $Y$ with $\langle a, b \rangle_\Gamma = \langle a, \Gamma^{-1} b \rangle$, and data
$y = A u^\dagger$ without noise. If the ensemble solves, for $t > 0$,

$$
\frac{du^{(j)}}{dt} = \frac1J \sum_{k=1}^J \big\langle A(u^{(k)} - \overline u), \, y - A u^{(j)} \big\rangle_\Gamma \, (u^{(k)} - \overline u),
$$

then for every $t > 0$ every entry $E_{lj}(t) = \langle A e^{(l)}, A e^{(j)} \rangle_\Gamma$ of the spread matrix,
with $e^{(j)} = u^{(j)} - \overline u$, satisfies

$$
|E_{lj}(t)| \le \frac{J}{2t} :
$$

the ensemble collapses onto its mean in the observed directions, with a bound that grows linearly in
the ensemble size.
Schillings and Stuart state $\|E(t)\| = O(J t^{-1})$; the explicit constant is what their proof gives.

The equation is the continuous-time limit of the EKI step (with $\Gamma \mapsto h^{-1}\Gamma$, $h \to 0$) and
is a gradient flow of $\Phi(u; y) = \frac12 \|\Gamma^{-1/2}(y - Au)\|^2$ preconditioned by the empirical
covariance. The proof shows $\frac{d}{dt} E = -\frac2J E^2$, so the eigenvalues of $E(t)$ are
$(2(t - s)/J + 1/\lambda(s))^{-1} \le J/(2(t - s))$ for $0 < s < t$ (or $0$), and the entries of a positive
semidefinite matrix are bounded by its largest eigenvalue. Any constant ensemble satisfies the hypotheses.

## Background

- [Invariant subspace property of ensemble Kalman inversion](eki-mem-span.md): the discrete-time
  subspace property, which also makes the continuous-time dynamics finite-dimensional.

## Sources

- Claudia Schillings and Andrew M. Stuart, *Analysis of the ensemble Kalman filter for inverse problems*, SIAM J. Numer. Anal. 55 (2017), no. 3, 1264–1290, DOI 10.1137/16M105959X; arXiv:1602.02020, equations (8)-(10) and Theorem 3.
