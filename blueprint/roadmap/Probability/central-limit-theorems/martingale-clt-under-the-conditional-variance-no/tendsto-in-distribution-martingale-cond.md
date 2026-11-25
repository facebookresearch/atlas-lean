# Martingale CLT under the conditional-variance normalization

**Martingale CLT under the conditional-variance normalization** (Brown 1971; Hall–Heyde
Corollary 3.1 with a constant limit). Let row `n` of `X` be a square-integrable martingale
difference sequence for the filtration `F n` (the partial sums `∑_{j<k} X n j` form a
martingale; a finite row is extended by zeros). If the **predictable** quadratic variation
`∑_{k<r n} E[X n k² | F n k]` of row `n` tends to `v` in probability and the **conditional Lindeberg condition**
`∑_{k<r n} E[X n k² 1{ε < |X n k|} | F n k] → 0` in probability holds for every `ε > 0`, then
`∑_{k<r n} X n k → N(0, v)` in distribution.

Compared with `tendstoInDistribution_martingale_mcLeish`, the realized quadratic variation
`∑ X n k²` is replaced by the predictable one, and McLeish's maximal-moment condition is not
assumed.

Proof: cut each row predictably, keeping increment `k` while `∑_{j ≤ k} E[X n j² | F n j]`
stays `≤ v + 1`. The cut row is still a martingale difference sequence, has
`E[∑ X'²] ≤ v + 1` (so McLeish's (a)), its maximal increment tends to `0` (McLeish's (b),
from the conditional Lindeberg condition), and its realized quadratic variation tends to `v`
(McLeish's (c)): the big jumps are controlled by the conditional Lindeberg condition and the
centred small jumps form a martingale with `L²` norm at most `ε² (v + 1)`. McLeish's theorem
applies to the cut row, which agrees with the original one outside an event of vanishing
probability.
