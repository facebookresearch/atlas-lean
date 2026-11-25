# Wbar δ comp σ succ

Successor relation for the total operators: `σ i ≫ δ i.succ = 𝟙`.
The degeneracy index is never `0` after succession, so no `wbarσ_zero`
rewrite is needed. At `i = last` the face is outer-last (pure transport)
and the index equality is direct by `ext`; otherwise both operators are
interior and `wChainSucc` applies. Coefficients are pure transports in all
cases.
