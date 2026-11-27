# Collapsing hash functions and collapse-binding commitments

A hash family $\{H_k\}$ is *collapsing* if no efficient quantum adversary can distinguish the following two experiments: the adversary prepares a register $X$ (in superposition) and a classical claimed value $y$ such that measuring $H_k(X)$ would yield $y$; then either (a) $X$ is returned unchanged, or (b) $X$ is measured in the computational basis before being returned. A commitment is *collapse-binding* if the analogous property holds for the opening register given the commitment. Collapsing strengthens collision resistance for quantum adversaries: it implies collision resistance, and it is what makes binding and rewinding arguments work against quantum adversaries.

## Depends on

- [The binding experiment](../../signatures-and-protocols/commitment-schemes/the-computational-binding-game-for-keyed-commitm/binding-game.md)
- [The quantum random oracle model](quantum-random-oracle-model.md)

## Sources

- Dominique Unruh, "Computationally Binding Quantum Commitments", EUROCRYPT (2016), IACR ePrint 2015/361.
