# Gating variables starting between 0 and 1 stay between 0 and 1

Let $\alpha, \beta \colon \mathbb{R} \to \mathbb{R}$ be positive at every voltage, let
$V \colon \mathbb{R} \to \mathbb{R}$ be any function (a voltage trace, with no regularity assumed)
and let $y \colon \mathbb{R} \to \mathbb{R}$ be differentiable at every $t \ge 0$ with

$$y'(t) = \alpha(V(t))\,(1 - y(t)) - \beta(V(t))\,y(t),$$

the [gating kinetics](gate.md) along $V$. If $y(0) \in [0, 1]$, then $y(t) \in [0, 1]$ for every
$t \ge 0$.
