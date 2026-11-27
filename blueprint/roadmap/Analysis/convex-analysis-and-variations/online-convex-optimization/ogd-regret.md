# Zinkevich's regret bound for online gradient descent

Zinkevich's regret bound for projected online gradient descent:
with step size `η > 0`, a nonexpansive projection fixing the comparator `xstar`, and
subgradients satisfying the convexity inequality, the regret against
`xstar` over `T` rounds is at most
`‖x0 - xstar‖² / (2η) + (η / 2) ∑ ‖g t (x t)‖²`.
