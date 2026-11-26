# Basic reproduction number in periodic environments

**Setting.** Write the infected compartments $x \in \mathbb{R}^n$ of an epidemic model with
$\omega$-periodic coefficients, linearized at a disease-free periodic solution, as

$$\dot x = \bigl(F(t) - V(t)\bigr) x,$$

where $F(t) \ge 0$ (entrywise) is the $\omega$-periodic matrix of new-infection rates and $-V(t)$ is
$\omega$-periodic and cooperative (nonnegative off-diagonal entries), describing transitions and
removals. Let $Y(t, s)$, $t \ge s$, be the evolution operator of $\dot y = -V(t) y$, and assume it is
exponentially stable ($\lVert Y(t, s) \rVert \le K e^{-\alpha(t - s)}$ for some $K, \alpha > 0$).

**Next infection operator.** On the Banach space $C_\omega$ of continuous $\omega$-periodic functions
$\mathbb{R} \to \mathbb{R}^n$ with the maximum norm, define

$$(L\Gamma)(t) = \int_0^\infty Y(t, t - a)\, F(t - a)\, \Gamma(t - a)\, da, \qquad \Gamma \in C_\omega .$$

If $\Gamma(s)$ is the density of infectious individuals introduced at time $s$, then $(L\Gamma)(t)$ is
the density of new infections they generate over their infectious periods, distributed in time.
The **basic reproduction number** is the spectral radius

$$\mathcal{R}_0 = \rho(L).$$

**Threshold theorem.** Let $\Phi_{F-V}(t)$ be the principal fundamental matrix of
$\dot x = (F(t) - V(t))x$. Then

$$\mathcal{R}_0 < 1 \iff \rho\bigl(\Phi_{F-V}(\omega)\bigr) < 1, \qquad
\mathcal{R}_0 = 1 \iff \rho\bigl(\Phi_{F-V}(\omega)\bigr) = 1, \qquad
\mathcal{R}_0 > 1 \iff \rho\bigl(\Phi_{F-V}(\omega)\bigr) > 1,$$

so the disease-free periodic solution is locally asymptotically stable if $\mathcal{R}_0 < 1$ and
unstable if $\mathcal{R}_0 > 1$.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

The operator $L$ generalizes the next-generation matrix $F V^{-1}$: for constant coefficients,
$Y(t, s) = e^{-V(t - s)}$ and $\int_0^\infty e^{-Va}\, da = V^{-1}$, so $\rho(L) = \rho(F V^{-1})$.
Replacing $\mathcal{R}_0$ by the time-averaged autonomous value can over- or underestimate the
threshold. The link to the monodromy matrix is Floquet theory: with
$\nu = \omega^{-1}\ln \rho(\Phi_{F-V}(\omega))$ and $F - V$ cooperative and irreducible, there is a
positive $\omega$-periodic $v(t)$ such that $e^{\nu t} v(t)$ solves the linear system, so infections
grow or decay at exponential rate $\nu$, and $\nu < 0$ exactly when $\mathcal{R}_0 < 1$. Comparison
arguments built on this solution give global attractivity of the disease-free periodic solution when
$\mathcal{R}_0 < 1$ and, with uniform persistence theory, existence of a positive periodic solution
when $\mathcal{R}_0 > 1$. Numerically, $\rho(L)$ is computed by discretizing the kernel over one
period, or as the value of $\lambda$ for which $\rho(\Phi_{F/\lambda - V}(\omega)) = 1$. In a
brucellosis model with seasonally varying transmission and bacterial shedding in livestock, humans,
wildlife and the environment, this yields global stability of the disease-free solution for
$\mathcal{R}_0 < 1$ and a positive periodic endemic solution for $\mathcal{R}_0 > 1$.

## Sources

- W. Wang, X.-Q. Zhao, "Threshold dynamics for compartmental epidemic models in periodic
  environments", Journal of Dynamics and Differential Equations 20 (2008) 699-717, Theorem 2.2,
  <https://doi.org/10.1007/s10884-008-9111-8>.
- N. Nyerere, L. S. Luboobi, S. C. Mpeshe, G. M. Shirima, "Modeling the Impact of Seasonal Weather
  Variations on the Infectiology of Brucellosis", Computational and Mathematical Methods in Medicine
  2020 (2020) 8972063, Eqs. (21)-(31), Lemma 1, Theorems 1-2,
  <https://doi.org/10.1155/2020/8972063> (PMC7586161).
