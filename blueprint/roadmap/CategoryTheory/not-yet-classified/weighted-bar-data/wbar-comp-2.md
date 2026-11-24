# Wbar δ comp δ

`δδ` for the total face operator: omitting `j.succ` then `i` agrees with
omitting `i.castSucc` then `j`, for `i ≤ j`. Dispatch on endpoints: both zero
is `wbar_δ_comp_δ_zero_zero`, zero against last is the accepted outer
interchange, zero against interior is `wbar_δ_comp_δ_zero_interior`, last
against last is `wbar_δ_comp_δ_last_last`, interior against last is
`wbar_δ_comp_δ_interior_last`, and interior against interior is
`wbar_δ_comp_δ_interior`. The `j = 0` subcase under interior `i` is
impossible by value bounds.
