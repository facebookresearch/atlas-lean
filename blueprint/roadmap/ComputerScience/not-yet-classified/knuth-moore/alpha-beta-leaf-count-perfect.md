# Knuth and Moore's best case

On a uniform tree of branching factor `k` and depth `d` with
perfectly ordered moves and a minimax value strictly between `⊥` and `⊤`, alpha-beta with the full
window evaluates exactly `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1` leaves.
