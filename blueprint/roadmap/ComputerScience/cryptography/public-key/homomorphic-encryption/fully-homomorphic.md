# Fully Homomorphic

Over a fixed finite gate signature, the interpretation on the declared message space at each security parameter must be functionally complete: every single-output function at every arity, including zero, is computed by a circuit. The scheme must [compactly evaluate every circuit over the basis](evaluates-basis.md), without a depth cutoff. In addition, key generation, encryption, decryption and evaluation must have [uniform polynomial-time realizations](polynomial-time.md) with no level parameter. The evaluator's budget includes the number of inputs and gates; the budget for the other three algorithms depends only on the security parameter.

This is Definition 2.1.4 of Gentry's *A Fully Homomorphic Encryption Scheme* (2009), with the efficient-algorithm setup of §2.1, in the [common-space model](spaces.md). It is not a secrecy condition.
