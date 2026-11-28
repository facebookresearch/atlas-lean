# Finite Horizon Greedy

Backward-recursion (greedy) policy: with `k + 1` steps remaining, act
greedily with respect to the `k`-step finite-horizon value. At `k = 0` the
action is irrelevant (no reward is collected); an arbitrary action is used.
