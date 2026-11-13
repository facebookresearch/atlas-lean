# Run Coins

Run an oracle computation against the randomized oracle `x ↦ O x ρ` on presampled coins:
the `i`-th query is answered with the `i`-th coin of the list (and with `default` once the list
is exhausted). A reduction that answers its adversary's encryption queries itself does this
(Katz and Lindell, proof of Proposition 11.3).
