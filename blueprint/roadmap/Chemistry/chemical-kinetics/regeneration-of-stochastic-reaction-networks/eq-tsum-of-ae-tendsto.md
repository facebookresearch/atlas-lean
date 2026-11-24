# Identification of the limit

Let `w` be a probability law balancing the rate-weighted
jump kernel (`w Q = 0`) with `∑ w q < ∞`, and let the chain be non-explosive from every state.
If from every initial state the time averages of `0 ≤ g ≤ 1` converge almost surely to the same
constant `L`, then `L = ∑_x w(x) g(x)`. The proof passes to Abel means (Abelian theorem), takes
expectations (bounded convergence), averages over `w` (dominated convergence), and uses the
resolvent identity `tsum_mul_lintegral_abelSum`.
