# Ogd regret

Zinkevich's regret bound for projected online gradient descent:
with a nonexpansive projection fixing the comparator `xstar`, and
subgradients satisfying the convexity inequality, the regret against
`xstar` over `T` rounds is at most
`‖x0 - xstar‖² / (2η) + (η / 2) ∑ ‖g t (x t)‖²`.
