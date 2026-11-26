# Efficiency of the data-driven one-step ODE estimator

**Setting.** Let $x(\eta,t)\in\mathbb R^d$ solve an ODE system $\dot x=F(x;\theta)$, $x(0)=\xi$, with full parameter $\eta=(\xi,\theta)\in H\subset\mathbb R^{d+p}$, and observe

$$Y_{ij}=x_i(\eta_0,t_j)+\epsilon_{ij},\qquad i=1,\dots,d,\ j=1,\dots,n .$$

Let $x'_\eta(\eta,t)$ be the $d\times(d+p)$ Jacobian of the solution with respect to $\eta$ and define the least-squares score

$$\Psi_n(\eta)=\sum_{j=1}^n x'_\eta(\eta,t_j)^{\top}\big(Y_j-x(\eta,t_j)\big).$$

Given a preliminary estimator $\hat\eta_n$ (for instance a smooth-and-match or integral estimator that avoids numerical integration), *Le Cam's one-step estimator* is a single Newton step on $\Psi_n$,

$$\bar\eta_n=\hat\eta_n-\Big(\tfrac{d}{d\eta}\Psi_n(\hat\eta_n)\Big)^{-1}\Psi_n(\hat\eta_n).$$

For a grid $\rho_n(1),\dots,\rho_n(N)$ of smoothing parameters, the *data-driven* version $\bar\eta_n^{*}$ picks, among the $N$ one-step estimators started from $\hat\eta_{\rho_n(k)}$, the one with the smallest residual sum of squares.

**Theorem 1 (asymptotic efficiency).** Assume: the $t_j$ are i.i.d. with distribution $F_T$ on $[0,T]$; the $\epsilon_{ij}$ are i.i.d. with mean $0$ and variance $\sigma^2>0$, independent of the $t_j$; $H$ is compact; third partial derivatives of $x(\eta,t)$ in $\eta$ exist and are continuous in $(\eta,t)$; the information matrix

$$I(\eta)=\frac1{\sigma^2}\sum_{i=1}^d\int_0^T\Big(\tfrac{d}{d\eta}x_i(\eta,t)\Big)^{\top}\Big(\tfrac{d}{d\eta}x_i(\eta,t)\Big)\,dF_T(t)$$

is nonsingular; and every deterministic choice $\rho_n$ in the grid gives a $\sqrt n$-consistent preliminary estimator. Then

$$\sqrt n\,(\bar\eta_n^{*}-\eta_0)\xrightarrow{d}\mathcal N\big(0,\ I(\eta_0)^{-1}\big),$$

the same limit as the nonlinear least-squares estimator. The conclusion still holds if $\tfrac{d}{d\eta}\Psi_n(\hat\eta_n)$ is replaced by the Gauss-Newton matrix $-\sum_j x'_\eta(\hat\eta_n,t_j)^{\top}x'_\eta(\hat\eta_n,t_j)$, which avoids second derivatives of the solution.

## Expansion

A Taylor expansion of $\Psi_n$ around $\eta_0$ shows that one Newton step from a $\sqrt n$-consistent start removes the first-order error: $\sqrt n(\bar\eta_n-\eta_0)=-(\tfrac1n\tfrac{d}{d\eta}\Psi_n)^{-1}\tfrac1{\sqrt n}\Psi_n(\eta_0)+o_P(1)$, and $\tfrac1n\tfrac{d}{d\eta}\Psi_n\to-\sigma^2 I(\eta_0)$ while $\tfrac1{\sqrt n}\Psi_n(\eta_0)\to\mathcal N(0,\sigma^4I(\eta_0))$. Since each of the finitely many candidates is asymptotically equivalent to the least-squares estimator, so is the residual-minimizing selection. Computationally the method needs one integration of the ODE and its sensitivity equations instead of repeated integrations inside an iterative optimizer.

## Sources

- Dattner I, Gugushvili S, "Application of one-step method to parameter estimation in ODE models", Statistica Neerlandica (2018), Equations (4)-(13), Theorem 1 and Remark 4, <https://doi.org/10.1111/stan.12124>, PMCID PMC5993282.
