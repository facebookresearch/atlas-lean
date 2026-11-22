# Peng's central limit theorem under a sublinear expectation

Let $(\Omega, \mathcal{H}, \mathbb{E})$ be a sublinear expectation space and let
$X_0, X_1, \dots \in \mathcal{H}$ be real random variables such that, for every $i$, $X_{i+1}$
has the same distribution as $X_i$ and $X_{i+1}$ is independent from $(X_0, \dots, X_i)$, and
such that $X_0$ has no mean uncertainty: $\mathbb{E}[X_0] = \mathbb{E}[-X_0] = 0$. Let $\xi$ be a
G-normally distributed random variable on a sublinear expectation space
$(\Omega', \mathcal{H}', \mathbb{E}')$ with the same upper and lower variances,
$\mathbb{E}'[\xi^2] = \mathbb{E}[X_0^2]$ and $\mathbb{E}'[-\xi^2] = \mathbb{E}[-X_0^2]$. Then
for every Lipschitz function $\varphi : \mathbb{R} \to \mathbb{R}$,

$$\mathbb{E}\Big[\varphi\Big(\frac{X_0 + \dots + X_{n-1}}{\sqrt{n}}\Big)\Big] \to \mathbb{E}'[\varphi(\xi)] \qquad (n \to \infty).$$

Identical distribution and independence are meant in Peng's sense for sublinear expectations.

## Background

- [Lindeberg–Feller central limit theorem](../lindeberg-feller-central-limit-theorem/README.md):
  the classical central limit theorem, recovered when the variance has no uncertainty
  ($\mathbb{E}[X_0^2] = -\mathbb{E}[-X_0^2]$). Peng's proof is very different from the classical
  one: it rests on the G-heat equation and Krylov's $C^{1,2}$ estimates for fully nonlinear
  parabolic PDEs (Proc. ICM 2010, the paragraph after Theorem 2.4).
- [A G-normal random variable has zero upper mean](../../foundations/sublinear-expectations-and-model-uncertainty/expectation-eq-zero.md):
  the reason for the hypothesis $\mathbb{E}[X_0] = \mathbb{E}[-X_0] = 0$.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010 (published by Springer, 2019), Chapter II, Theorem 3.3 with $d = 1$;
  by Remark 3.4 the limit is the G-normal law $N(\{0\} \times [\underline{\sigma}^2, \overline{\sigma}^2])$.
