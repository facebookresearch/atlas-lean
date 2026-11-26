# Vandermonde's identity

For all natural numbers $m$, $n$ and $k$,

$$\binom{m+n}{k} = \sum_{\substack{i + j = k}} \binom{m}{i}\binom{n}{j},$$

the sum running over the pairs $(i, j)$ of natural numbers with $i + j = k$.

## Sources

- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842: [Nat.add_choose_eq](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/Nat/Choose/Vandermonde.lean#L28 "Nat.add_choose_eq").
