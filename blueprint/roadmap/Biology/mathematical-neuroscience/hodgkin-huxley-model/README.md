# Hodgkin–Huxley model

## The function x/(eˣ − 1) and its removable singularity

- [The function x/(eˣ − 1) extended by 1 at 0](vtrap.md)
- [The extension φ of x/(eˣ − 1) is positive](vtrap-pos.md)
- [The extension φ of x/(eˣ − 1) is C¹](cont-diff-vtrap.md)
- [Away from 0 the extension φ equals x/(eˣ − 1)](vtrap-of-ne.md)
- [Derivative of x/(eˣ − 1) away from 0](has-deriv-at-vtrap.md)

## Rate functions

- [Sodium activation opening rate α_m](alpha-m.md)
- [Sodium activation closing rate β_m](beta-m.md)
- [Sodium inactivation recovery rate α_h](alpha-h.md)
- [Sodium inactivation rate β_h](beta-h.md)
- [Potassium activation opening rate α_n](alpha-n.md)
- [Potassium activation closing rate β_n](beta-n.md)
- [The sodium activation opening rate α_m is positive](alpha-m-pos.md)
- [The sodium activation opening rate α_m is C¹](cont-diff-alpha-m.md)

## Gating kinetics and steady states

- [Gating kinetics α(V)(1 − y) − β(V)y](gate.md)
- [Steady state α/(α + β) of the gating kinetics](steady.md)
- [With positive rates, gating kinetics vanish exactly at steady state](gate-eq-zero-iff.md)
- [With positive rates the steady state lies in (0, 1)](steady-mem-ioo.md)

## Parameters, vector field and solutions

- [Hodgkin–Huxley membrane parameters](params.md)
- [Valid Hodgkin–Huxley parameters](valid.md)
- [Total ionic current of the Hodgkin–Huxley membrane](ionic.md)
- [The Hodgkin–Huxley vector field](field.md)
- [Solution of the Hodgkin–Huxley equations for all t ≥ 0](is-solution.md)
- [The Hodgkin–Huxley vector field is C¹](cont-diff-field.md)

## Forward invariance

- [Gating variables starting between 0 and 1 stay between 0 and 1](gate-mem-icc.md)
- [Box of states with voltage in an interval and gating between 0 and 1](box.md)
- [Trapping voltage interval](is-trapping.md)
- [A trapping interval is nonempty](le.md)
- [For valid parameters every voltage lies in a trapping interval](exists-is-trapping.md)
- [For valid parameters, solutions starting in a trapping box stay in it](mem-box.md)

## Global existence and uniqueness

- [Global existence in a trapping box for valid parameters](exists-is-solution-mem-box.md)
- [The gating cube: m, h and n between 0 and 1](gating-region.md)
- [Global existence and boundedness for valid parameters](exists-is-solution.md)
- [For valid parameters, solutions from the gating cube stay bounded](bounded.md)
- [Forward uniqueness from the gating cube for valid parameters](eq-of-eq.md)

## Equilibria

- [Equilibria of the Hodgkin–Huxley equations for valid parameters](field-eq-zero-iff.md)

## Linearization

- [Jacobian matrix of the Hodgkin–Huxley vector field](jac.md)
- [The Jacobian matrix is the derivative of the Hodgkin–Huxley field](has-fderiv-at-field.md)

## A Hurwitz criterion for arrowhead matrices

- [Hurwitz criterion for a 4 × 4 arrowhead matrix](is-hurwitz-arrowhead.md)

## The squid giant axon: resting state and its stability

- [Sodium activation opening rate at rest](alpha-m-zero.md)
- [Derivative of the sodium activation opening rate at rest](has-deriv-at-alpha-m-zero.md)
- [Resting sodium activation m∞(0)](m-rest.md)
- [Resting sodium inactivation h∞(0)](h-rest.md)
- [Resting potassium activation n∞(0)](n-rest.md)
- [Leak reversal potential of the squid giant axon](squid-el.md)
- [Squid giant axon parameters](squid.md)
- [The squid parameters are valid](squid-valid.md)
- [The resting state (0, m∞(0), h∞(0), n∞(0))](rest.md)
- [The resting state is an equilibrium of the squid equations](field-squid-rest.md)
- [The resting sodium activation lies in (0, 1)](m-rest-mem.md)
- [The resting sodium activation is at most 0.054](m-rest-le.md)
- [The resting sodium inactivation is at most 0.6](h-rest-le.md)
- [The resting potassium activation is at least 0.3](n-rest-ge.md)
- [Bounds on the derivative of α_m at rest](deriv-alpha-m-zero-le.md)
- [The Jacobian at the squid resting state is Hurwitz](jac-squid-rest-is-hurwitz.md)
- [Local exponential stability of the squid resting state](rest-exponentially-stable.md)

## Bounds on the derivative of x/(eˣ − 1)

- [The extension φ of x/(eˣ − 1) has φ′(0) = −1/2](deriv-vtrap-zero.md)
- [The extension φ of x/(eˣ − 1) has φ′ ≤ 0 everywhere](neg-deriv-vtrap-nonneg.md)
- [The extension φ of x/(eˣ − 1) satisfies −φ′ ≤ φ](neg-deriv-vtrap-le.md)
- [For x ≥ 0 the extension φ of x/(eˣ − 1) satisfies φ(x)/2 ≤ −φ′(x)](half-vtrap-le-neg-deriv.md)
- [For x ≥ 0 the extension φ of x/(eˣ − 1) has −φ′(x) ≤ (1/2 + x/12)φ(x)](neg-deriv-vtrap-le-pade.md)
- [For x ≤ 0 the extension φ of x/(eˣ − 1) has (1/2 + x/12)φ(x) ≤ −φ′(x)](pade-vtrap-le-neg-deriv.md)

## Steady states and their logarithmic derivatives

- [Derivative of a gating steady state](has-deriv-at-steady.md)
- [Steady-state sodium activation m∞](m-inf.md)
- [Steady-state sodium inactivation h∞](h-inf.md)
- [Steady-state potassium activation n∞](n-inf.md)
- [Logarithmic derivative λ_m of α_m/β_m](lam-m.md)
- [Logarithmic derivative λ_h of α_h/β_h](lam-h.md)
- [Logarithmic derivative λ_n of α_n/β_n](lam-n.md)

## Bounds on the logarithmic derivatives

- [Upper bound on λ_m for p ≤ V ≤ q with q ≤ 25](lam-m-le-of-le.md)
- [Lower bound λ_n ≥ 1/80 + 1/20 for V ≤ 10](lam-n-ge-of-le.md)
- [Lower bound on λ_n for p ≤ V ≤ q with q ≥ 10](lam-n-ge-of-ge.md)

## Monotonicity of the steady states

- [Steady-state sodium activation m∞ is strictly increasing](strict-mono-m-inf.md)
- [Steady-state sodium inactivation h∞ is strictly decreasing](strict-anti-h-inf.md)
- [Steady-state potassium activation n∞ is strictly increasing](strict-mono-n-inf.md)

## The steady-state current and its derivative

- [Steady-state current–voltage relation I∞](steady-current.md)
- [Termwise derivative formula of the steady-state current](steady-current-deriv.md)

## Monotonicity of the squid steady-state current

- [The squid I∞ termwise derivative formula is positive for −12 ≤ V ≤ 115](steady-current-deriv-squid-pos.md)
- [The squid steady-state current increases strictly for −12 ≤ V ≤ 115](strict-mono-on-steady-current-squid.md)

## Uniqueness of the squid equilibrium

- [The squid leak potential lies strictly between E_K and E_Na](squid-el-mem.md)
- [The squid steady-state current is negative for V ≤ −12](steady-current-squid-neg.md)
- [The squid steady-state current is positive for V ≥ 115](steady-current-squid-pos.md)
- [The squid steady-state current vanishes at rest](steady-current-squid-zero.md)
- [Rest is the only zero of the squid steady-state current](steady-current-squid-eq-zero-iff.md)
- [The squid resting state is the only equilibrium](field-squid-eq-zero-iff.md)
