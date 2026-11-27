# Scaled Loss

The losses fed to copy `j` in the Blum–Mansour reduction: for arbitrary real arrays `p` and
`loss` indexed by time and action, the scaled loss of copy `j` at time `t` on action `a` is
`p t j * loss t a`. When each `p t` is a probability distribution, this is the true loss scaled
by the master's probability of `j` at time `t`.
