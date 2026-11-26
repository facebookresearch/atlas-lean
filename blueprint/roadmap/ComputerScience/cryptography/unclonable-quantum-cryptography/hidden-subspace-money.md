# Public-key quantum money from hidden subspaces relative to a classical oracle

Relative to a classical oracle (providing membership oracles for $A$ and $A^{\perp}$ indexed by a serial number, e.g., obfuscated or random-oracle-indexed), the scheme in which the banknote with serial $s$ is the subspace state $|A_s\rangle$ and verification projects onto $|A_s\rangle$ using the two membership oracles is a secure public-key quantum money scheme: any counterfeiter making polynomially many queries succeeds with negligible probability. Instantiating the oracles with indistinguishability obfuscation of membership circuits yields public-key quantum money in the standard model assuming iO and quantum-secure one-way functions.

## Proof sketch

Security relative to the oracle follows from the query lower bound for duplicating subspace states, after showing that the serial-number indexing does not help (random self-reducibility of the subspace family). The iO instantiation replaces oracle access with obfuscated circuits; security uses subspace-hiding obfuscation and the direct-product hardness of subspace states (later established in the coset-state framework).

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [Public-key quantum money and quantum lightning](public-key-quantum-money.md)

## Proof depends on

- [Query lower bound for duplicating subspace states](subspace-state-unclonability.md)

## Sources

- Scott Aaronson, Paul Christiano, "Quantum Money from Hidden Subspaces", STOC (2012), arXiv:1203.4740.
- Mark Zhandry, "Quantum Lightning Never Strikes the Same State Twice", EUROCRYPT (2019).
