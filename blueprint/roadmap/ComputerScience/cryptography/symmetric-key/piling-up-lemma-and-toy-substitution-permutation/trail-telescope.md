# Trail error bits telescope to boundary parities

For a substitution-permutation network whose states satisfy `x (i + 1) =
spnRound (k i) (S i) (π i) (x i)`, and masks `u i`, the exclusive or of the
trail error bits over rounds `0, …, r - 1` equals the parity of `x 0` under `u
0` xor the parity of `x r` under `u r`, with no key term.
