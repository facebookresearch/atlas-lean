# Collision resistance implies target collision resistance

Let `X n` and `Y n` have decidable equality, and let `X n` and the coin spaces
`R n` be nonempty for every security parameter `n`. If the reduction
`tcrToColl` maps every admissible target-collision adversary to an admissible
collision finder, then collision resistance of the hash family `H` implies its
target collision resistance, with the same advantage.
