# Computational soundness of formal encryption

Consider formal expressions built from bits, keys, pairing and symmetric encryption, and the formal equivalence $M \cong N$ under which expressions with equal patterns up to renaming of keys (undecryptable ciphertexts replaced by a placeholder) are equivalent. If $M$ and $N$ are acyclic (no key is encrypted, directly or through a chain of encryptions, under itself) and $M \cong N$, then their computational interpretations under a type-0 secure symmetric encryption scheme are computationally indistinguishable. A scheme $(\mathcal{K}, \mathcal{E}, \mathcal{D})$ is *type-0 secure* if for independent keys $k, k'$ every efficient adversary has negligible advantage in distinguishing the pair of oracles $(\mathcal{E}_k(\cdot), \mathcal{E}_{k'}(\cdot))$ from the pair $(\mathcal{E}_k(0), \mathcal{E}_k(0))$ that encrypts a fixed message $0$ under a single key; such a scheme conceals which key was used, message lengths, and repetitions.

## Depends on

- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)

## Proof depends on

- [The hybrid step](../../security-games/games-and-advantages/advantage-hybrid-uniform.md)

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Dolev-Yao intruder deduction.

## Sources

- M. Abadi and P. Rogaway, "Reconciling two views of cryptography (the computational soundness of formal encryption)", *Journal of Cryptology* 15(2):103–127, 2002
