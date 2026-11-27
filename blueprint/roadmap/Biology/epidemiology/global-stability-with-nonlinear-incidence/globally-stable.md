# Globally Stable

Stability of `e` within the state space `D` of the model: `e` is Lyapunov stable for the
solutions of `x' = F x` on `[0, ∞)` (`IsIntegralCurveOn x (fun _ => F) (Set.Ici 0)`, with the
derivative at `0` taken within `[0, ∞)`) that stay in `D`, and attracts every such solution that
starts in `A`. (The incidence functions are only constrained on `[0, ∞)`, so the models live on the
nonnegative orthant; it is forward invariant for every solution of a locally Lipschitz
extension of the vector field.)
