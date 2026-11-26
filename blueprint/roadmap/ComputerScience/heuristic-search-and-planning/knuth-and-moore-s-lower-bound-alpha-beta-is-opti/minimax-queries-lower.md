# Knuth and Moore's lower bound

Every query algorithm that computes the minimax value of a
uniform shape of branching factor `k` and depth `d` with distinct leaf variables reads at least
`k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` distinct leaves on every input whose value lies strictly between
`⊥` and `⊤`.
