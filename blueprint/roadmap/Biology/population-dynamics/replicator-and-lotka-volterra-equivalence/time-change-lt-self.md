# With two strategies or more the Lotka–Volterra time runs slower

Let `ι` be a finite nonempty set, so that the strategies `ι ∪ {o}` number at least two, `f` a
continuous fitness function, and `x` a [replicator solution](../replicator-dynamics/is-solution.md)
of `x_k' = x_k (f_k(x) - f̄(x))` for `t ≥ 0` starting in the interior of the simplex: every
`x_k(0) > 0` and `∑_k x_k(0) = 1`. Then the [Lotka–Volterra time](time-change.md) satisfies
`τ(t) < t` for every `t > 0`: time is not preserved.
