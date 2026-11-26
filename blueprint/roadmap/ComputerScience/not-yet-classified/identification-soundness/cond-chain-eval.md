# Evaluating the conditional chain of lines 6 and 7 of ID

Let `V` and `α` be finite
types, `p` a real-valued weight on the assignments `x : V → α`, `σ` an order of `V`, `D` and `S`
vertex sets and `P` an expression, and write `q` for the evaluation of `P` against `p`. The
conditional chain `condChain σ D S P` of lines 6 and 7 of ID (Shpitser and Pearl, AAAI 2006,
Fig. 3) evaluates at `x` to the product over `i ∈ S` of the ratios `q(v_i, v_{<i}) / q(v_{<i})`,
where `v_{<i}` are the vertices of `D` before `i` in `σ` and each term is the marginal of `q` that
fixes those vertices, and every vertex outside `D`, at their values in `x`. A ratio with
denominator `0` is `0` (real division).
