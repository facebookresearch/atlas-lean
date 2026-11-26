# Leveled evaluation over a finite basis

The family may evaluate circuits over a specified finite set of operations; the set need not be universal. One polynomially bounded decryption circuit at each security parameter implements decryption at every positive level. Each fixed level $d$ has one negligible bound for all arities and circuits through depth $d$ inclusive. The four algorithms have [uniform polynomial running time](polynomial-time.md) across levels, with input arity and gate count charged for evaluation.

Finiteness is a restriction of this runtime model, not a requirement stated by Gentry in Definition 2.1.5. For a fixed finite basis, both the encoded length of a gate name and the number of wires entering a gate are bounded independently of the circuit. With arbitrary gate types a single gate need not obey either bound. In Theorem 4.2.2 Gentry explicitly measures circuit size by the number of wires.
