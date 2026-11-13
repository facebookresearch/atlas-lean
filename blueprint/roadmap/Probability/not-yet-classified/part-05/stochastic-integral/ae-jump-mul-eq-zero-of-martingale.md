# A necessary condition for integration against the compensated process

Let `N` have unit
jumps and `M = martingalePart N` be its compensated process. If `N` is adapted, the
integrand `H_k = ΔN_k` is adapted but need not be predictable (adaptation is not implied by
`IsCountingProcess` or `HasUnitJumps`). If `H • M` is nevertheless a martingale, then a.e. `N`
can only jump
at steps where its compensator jumps by exactly `1` (`ΔN_{k+1} (1 - ΔA_{k+1}) = 0`): the
integral picks up `∑ ΔN (1 - ΔA) ≥ 0`, which has positive mean as soon as `N` has a
jump that is not fully predicted.
