# Weak solutions of the one-dimensional heat equation

On $\Omega = (0, 1)$ and a finite interval $t_0 < t_1$, let $\kappa(t, x)$ be measurable with $0 < \kappa_{\min} \le \kappa \le \kappa_{\max}$
almost everywhere, $f \in L^2(t_0, t_1; H^{-1}(\Omega))$ and $u_0 \in L^2(\Omega)$. Then $u_t = (\kappa u_x)_x + f$ with zero boundary values in
the $H^1_0$ sense and $u(t_0) = u_0$ has a unique weak solution $u \in L^2(t_0, t_1; H^1_0)$ with $u_t \in L^2(t_0, t_1; H^{-1})$, which has a
continuous $L^2$-valued representative attaining $u_0$ at $t_0$. For this representative and every $\tau\in[t_0,t_1]$,

$$\frac12\|u(\tau)\|_{L^2}^2+\int_{t_0}^{\tau}\int_\Omega\kappa|u_x|^2\,dx\,dt
=\frac12\|u_0\|_{L^2}^2+\int_{t_0}^{\tau}\langle f,u\rangle_{H^{-1},H^1_0}\,dt.$$

The variables are nondimensional; physical scales are restored separately.

## Depends on

## Proof depends on

## Expansion

Reuse the existing upstream parabolic existence and uniqueness results rather than build another Galerkin or Lions proof. Check
compatibility of the selected libraries and the exact coefficient, forcing, trace and energy-identity hypotheses before claiming a
formalized specialization. In particular, reconcile almost-everywhere coefficient bounds with any pointwise-in-space ellipticity
condition by a justified choice of representative. The coefficient specialization, initial trace, energy identity and physical scaling
must be checked separately; this page does not claim that the integration work is complete.

## Sources

- L. C. Evans, *Partial Differential Equations*, 2nd edition, American Mathematical Society, 2010, Section 7.1.
