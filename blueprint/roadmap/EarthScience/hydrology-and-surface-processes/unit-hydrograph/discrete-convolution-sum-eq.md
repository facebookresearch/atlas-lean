# Total convolution response is the product of the totals

If the rainfall excess vanishes from step `n` on (`p i = 0` for `i ≥ n`) and the unit response
from step `m` on (`u j = 0` for `j ≥ m`), the total outflow of the
[discrete convolution](discrete-convolution.md) `q` over the steps `0 ≤ k < n + m` is the product
of the totals: `∑_{k < n + m} q k = (∑_{i < n} p i) * (∑_{j < m} u j)`. The horizon has one step
more than needed: its last step `k = n + m - 1` carries no outflow.
