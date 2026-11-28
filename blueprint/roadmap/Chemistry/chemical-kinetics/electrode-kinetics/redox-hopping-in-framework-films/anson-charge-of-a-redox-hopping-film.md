# Anson charge of a redox-hopping film

If the faradaic current after a potential step is $K/\sqrt{s}$ on a time window, its charge over the window is $2K(\sqrt{t} - \sqrt{t_0})$; for the Cottrell current from $s = 0$ the charge is $2nFAC\sqrt{D_{app}t/\pi}$.

Let a faradaic current, counted positive when the responding species is consumed, satisfy $i(s) = K/\sqrt{s}$ for
$t_0 \le s \le t$, with constants $K$ and $0 < t_0 < t$. Then

$$
\int_{t_0}^{t} i(s)\,ds = 2K\left(\sqrt{t} - \sqrt{t_0}\right),
$$

whatever the current before $t_0$. If $i(s) = K/\sqrt{s}$ holds for all $0 < s \le t$, the charge from the step is
$q(t) = 2K\sqrt{t}$. For the Cottrell current, $K = nFAC\sqrt{D_{app}/\pi}$ with $n > 0$ electrons per event,
Faraday constant $F = N_Ae$, electrode area $A > 0$, apparent diffusion coefficient $D_{app} > 0$ and $C$ the molar
concentration of the species convertible by the step (initial minus surface value; the total site concentration only if
every site is initially in the reacting state). Then

$$
q(t) = \frac{2nFAC\sqrt{D_{app}\,t}}{\sqrt{\pi}}, \qquad
D_{app} = \pi\left(\frac{\text{slope}}{2nFAC}\right)^2 \ (C \ne 0),
$$

where slope is the coefficient of $\sqrt{t}$. Measured charge also contains double-layer and surface contributions;
they add a constant intercept to $q$ against $\sqrt{t}$ only if they are effectively constant over the analysed window,
and ongoing charging or drift is not captured by an intercept. For a film of finite thickness the $K/\sqrt{s}$ law is an
approximation in an intermediate window, after charging and electron-transfer transients and before $\sqrt{D_{app}t}$
approaches the film thickness.

## Context

Graduate level. Anson analysis is used alongside chronoamperometry to measure apparent hopping diffusion coefficients of multivariate redox-active MOF films, being less sensitive to non-faradaic charging.

## Depends on

- [Cottrell equation](../cottrell-equation.md)

## Proof depends on

None.

## Expansion

$\int_{t_0}^t s^{-1/2}\,ds = 2(\sqrt t - \sqrt{t_0})$, and $\int_0^t s^{-1/2}\,ds = 2\sqrt{t}$ as a convergent
improper integral. The Cottrell coefficient follows from the generic equation with $c_0 - c_1 = N_AC$ (number
concentration from molar concentration), $D = D_{app}$ and $F = N_Ae$, with the same consumption-positive sign
convention.

## Sources

- S. Basak, L. Prince, Z. Du and A. J. Morris, "Tunable redox hopping charge transport and electrochromism in multivariate MOFs", *Chemical Science* (2026), [doi.org](https://doi.org/10.1039/d6sc02965e), PMC13322743, Eqs. (5) and (6).
