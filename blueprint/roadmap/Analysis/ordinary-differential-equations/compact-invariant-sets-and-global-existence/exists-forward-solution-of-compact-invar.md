# Exists forward solution of compact invariant

In a complete real normed space, let `F` be locally Lipschitz and `K` compact.
Fix an initial time `a` and point `x₀`. If every supplied solution through `x₀`
on each closed interval `Icc a b`, `a ≤ b`, stays in `K`, then there exists a
forward global solution through `x₀` which stays in `K`. Its ordinary derivative
is `F (x t)` at every `t ≥ a`, including the initial time. The singleton interval
case of the invariance premise already forces `x₀ ∈ K`.

This uses the existing compact-trapping continuation theorem. Its classical
finite-dimensional criterion is Teschl, *Ordinary Differential Equations and
Dynamical Systems*, §2.6, Corollaries 2.15–2.16.
