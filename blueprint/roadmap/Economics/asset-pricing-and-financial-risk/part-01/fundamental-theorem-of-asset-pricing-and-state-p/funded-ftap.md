# Fundamental theorem of asset pricing for funded gains

Take finitely many states `ω`, at least one, and finitely many assets `a`, where asset `a`
costs `p(a)` today and pays `X(a, ω)` in state `ω`, and a gross risk-free return `R` of any
sign. The following are equivalent:

- no portfolio `h` (a real vector indexed by the assets) has funded gain
  `∑_a h(a) (X(a, ω) - R p(a))` nonnegative in every state `ω` and strictly positive in some
  state;
- there is `q` with `q(ω) > 0` for every state `ω` and `∑_ω q(ω) = 1` such that
  `∑_ω q(ω) X(a, ω) = R p(a)` for every asset `a`.

This is the gain form of the theorem, the
[one-period fundamental theorem of asset pricing](../../../../Probability/martingales/fundamental-theorem-of-asset-pricing/one-period-fundamental-theorem-asset-pri-2.md)
(no portfolio of the gains `g(a, ω)` is nonnegative in every state and positive in some state
iff some strictly positive `q` summing to `1` gives `∑_ω q(ω) g(a, ω) = 0` for every asset),
applied to the funded gains
`g(a, ω) = X(a, ω) - R p(a)`: since `∑_ω q(ω) = 1`, `∑_ω q(ω) g(a, ω) = 0` iff
`∑_ω q(ω) X(a, ω) = R p(a)`. No sign hypothesis on `R` is needed.
