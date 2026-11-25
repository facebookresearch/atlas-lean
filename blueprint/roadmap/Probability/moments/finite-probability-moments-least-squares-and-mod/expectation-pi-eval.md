# Expectation pi eval

Assume that equality on `ι` is decidable; that `α` is finite; and that `ι` is finite. Assume `∑ a, p a = 1`.

Under the i.i.d. weight, each coordinate has law `p`.

In symbols: `expectation (fun ω : ι → α => ∏ k, p (ω k)) (fun ω => f (ω i)) = expectation p f`.
