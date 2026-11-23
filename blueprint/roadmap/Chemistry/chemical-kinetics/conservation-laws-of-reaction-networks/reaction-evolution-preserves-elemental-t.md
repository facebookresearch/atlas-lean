# Reaction trajectories keep every left-null weighted total constant

Let `S` be the real stoichiometric matrix of `n` species and `m` reactions, `l` a left-null vector
of `S` (`∑_i l_i S_ij = 0` for every reaction `j`) and `v` any rate law, a function from
concentration vectors to reaction rates. If a concentration trajectory `c` obeys
`c_i'(s) = ∑_j S_ij v_j(c(s))` for every species `i` at every real time `s`, then for every real
`t` the weighted total at time `t` equals the one at time `0`: `∑_i l_i c_i(t) = ∑_i l_i c_i(0)`.
