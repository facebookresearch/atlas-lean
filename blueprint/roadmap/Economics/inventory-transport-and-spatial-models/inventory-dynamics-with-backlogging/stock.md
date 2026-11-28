# Stock

Unsold stock carried into period `t`, starting from nonnegative `initial`. The scheduled
receipt comes from `initPipe` for `t < L` and from order `t - L` otherwise. The order at `t`
is placed before demand and received immediately if `L = 0`. Of the resulting available
stock, only its minimum with current demand is sold; no unmet demand is carried forward.
