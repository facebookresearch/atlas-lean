# Gradient flow identity

Gradient-flow identity: if a trajectory satisfies the gradient-flow ODE
at time `t` (in particular, the hypothesis holds at each positive time of
such a forward gradient-flow trajectory on `t ≥ 0`, and at `t = 0` when the
trajectory extends differentiably through `0`), the outputs evolve by the
negative NTK applied to the residual. The ODE at `t` and global `C¹`
regularity of `F` are hypotheses; existence and uniqueness of the flow, and
constancy of the NTK during training, are not claimed.
