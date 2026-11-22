# VaR of one loss is 0

At level `0.95`, the single loss (100 with probability 0.04)
has `VaR = 0`: the set `{x | 0.95 ≤ cdf x}` is `Ici 0`, whose infimum is `0`.

By `cdf_loss_single_eq`, the cdf is `0 < 0.95` below `0` and at least `0.96 ≥ 0.95`
from `0` on.
