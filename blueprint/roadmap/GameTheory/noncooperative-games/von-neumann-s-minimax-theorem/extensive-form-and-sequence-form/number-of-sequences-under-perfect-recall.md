# Number of sequences under perfect recall

If player $i$ has perfect recall, the map sending the empty sequence to itself and each pair $(h, c)$ with $c \in C_h$ to the sequence $\sigma_h c$ is a bijection onto the occurring sequences, so $|S_i| = 1 + \sum_{h \in H_i} |C_h|$. In particular the sequence form has size linear in the game tree, in contrast to the exponentially many pure strategies.

## Proof sketch

Perfect recall gives each information set a unique preceding sequence, so every nonempty sequence ends in a unique (information set, choice) pair.

## Depends on

- [Sequence form and realization plans](sequence-form-and-realization-plans.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
