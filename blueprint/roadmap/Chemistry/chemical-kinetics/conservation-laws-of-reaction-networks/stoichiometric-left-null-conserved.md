# Left-null weighted totals have zero derivative under the rate law

Let `S` be the real stoichiometric matrix of `n` species and `m` reactions, `l` a left-null vector
of `S` (`∑_i l_i S_ij = 0` for every reaction `j`) and `v` any rate law, a function from
concentration vectors to reaction rates. If at a time `t` each concentration of a trajectory `c`
has derivative `c_i'(t) = ∑_j S_ij v_j(c(t))`, then the weighted total `s ↦ ∑_i l_i c_i(s)` has
derivative `0` at `t`.
