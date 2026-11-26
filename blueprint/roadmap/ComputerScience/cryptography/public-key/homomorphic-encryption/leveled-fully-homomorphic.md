# Leveled Fully Homomorphic

For a fixed finite gate signature, the interpretation at every security parameter must be functionally complete, including constants at arity zero. The family must also satisfy [leveled evaluation over the specified basis](leveled-over-basis.md): the same polynomially bounded decryption circuit works across levels, level $d$ is correct for all circuits through depth $d$, and all four algorithms have uniform polynomial-time realizations.

Gentry's Definition 2.1.5 explicitly says “some specified set of gates.” Theorem 4.2.1 distinguishes evaluation for arbitrary specified gates from the case of a universal set. This is the universal case, specialized to the finite basis required by the [runtime convention](polynomial-time.md) and to the [common-space model](spaces.md).
