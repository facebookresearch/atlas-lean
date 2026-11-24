# A bare residual is not an error

Over all stiffnesses `k > 0`, with no lower bound, no
constant `C` makes `C |k u - F|` a bound on the state error, and for `F ≠ 0` none makes it a
bound on the compliance error: the trial `u = F / k + 1` has residual `k`, state error `1` and
compliance error `|F|`. This combines `not_exists_residual_state_error_bound`, which holds for
every `F`, and `not_exists_residual_compliance_error_bound`.
