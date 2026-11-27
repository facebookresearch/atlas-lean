# One step of Patterson's Taylor recursion

For a real function `f` and a real number `x`, let

`(S f)(x) = (d²/dx²)[x (1 - x) f(x) / 2] - f(x) / x`,

where a derivative that does not exist is taken to be `0` and `u / 0 = 0`, so that `(S f)(0)` is the
second-derivative term alone. The intended use is `0 < x < 1` with `f` twice differentiable. In
Patterson's Theorem 7, iterating `S` `n` times from `f` and evaluating at the present frequency `y`
gives the `n`-th derivative at `t = 0` of `F(y, f; t) = ∫₀¹ f(x) C(x, y; t) dx`, where `C` is the
transition density of the killed diffusion.

## Sources

- N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*, Genetics 169
  (2005), 1093–1104.
