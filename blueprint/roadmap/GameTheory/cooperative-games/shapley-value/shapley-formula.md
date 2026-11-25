# Shapley's formula

The value that pays player $i$ of a TU game $v$ on $n$ players

$$\varphi_i(v) = \sum_{S \ni i} \frac{(|S| - 1)!\,(n - |S|)!}{n!}\,\bigl(v(S) - v(S \setminus \{i\})\bigr),$$

the average of $i$'s marginal contributions $v(S) - v(S \setminus \{i\})$ when all orders of the
players are equally likely. It is linear in $v$.

## Background

- [Shapley weight](shapley-weight.md): the coefficients.

## Sources

- R. Serrano, "Cooperative games: core and Shapley value", CEMFI Working Paper 0709 (2007), §4.1, formula for $Sh_i(N, v)$ (secondary source).
