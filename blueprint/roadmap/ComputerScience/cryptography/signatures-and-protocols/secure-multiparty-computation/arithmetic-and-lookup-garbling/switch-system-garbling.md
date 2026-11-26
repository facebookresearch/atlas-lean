# Garbling switch systems for arithmetic circuits

A *switch system* over a commutative ring $R$ has input wires, internal wires carrying values in $R$, and gates that either add wires linearly or *switch*: they copy one wire to another when a control bit is set. Propagation from an input finds the values of some wires; every value found by propagation agrees with every satisfying assignment. In Heath's garbling of switch systems, labels live in an $R$-module with a global offset $\Delta$ of colour $1$, linear gates are free, and each switch is garbled with one hash-derived ciphertext. Then (i) for a well-formed system and an assignment satisfying it on input $x$, garbled evaluation tracks propagation, so every output wire on which propagation finds a value decodes to that value; (ii) under circular correlation robustness of the hash, the evaluator's view (gate material and input labels) is computationally simulatable, i.e. garbled switch systems are oblivious.

## Proof sketch

(i) Induct over gates in order: linear gates preserve the affine label invariant, and a switch either reveals the copied label or a pad. (ii) Every pad not decrypted by the evaluator is a hash at an inactive label, which CCR replaces by a uniform value.

## Depends on

- [Affine wire labels for arithmetic garbling](affine-wire-labels.md)
- [Circular correlation robust hash functions](../garbling-scheme-security/circular-correlation-robustness.md)

## Sources

- David Heath, "Efficient Arithmetic in Garbled Circuits", Advances in Cryptology – EUROCRYPT 2024, 2024.
