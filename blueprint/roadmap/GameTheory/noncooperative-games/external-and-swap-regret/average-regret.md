# Average Regret

For a horizon `T`, a finite nonempty set `K` of actions, plays `play : Fin T → K → ℝ` and losses `loss : Fin T → K → ℝ`, the average regret is the external regret divided by `T`, where the external regret is the play-weighted loss `∑ₜ ∑ₐ play t a · loss t a` minus the least cumulative loss `minₐ ∑ₜ loss t a` of a fixed action. For `T = 0` it is `0`, by the convention `x / 0 = 0`.
