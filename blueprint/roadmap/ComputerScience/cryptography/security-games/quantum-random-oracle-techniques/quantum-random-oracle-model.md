# The quantum random oracle model

In the *quantum random oracle model (QROM)*, a uniformly random function $H:\{0,1\}^{n}\to\{0,1\}^{m}$ is sampled, and all parties, including the adversary, may query it in superposition through the unitary $O_H:|x\rangle|y\rangle\mapsto|x\rangle|y\oplus H(x)\rangle$. A scheme is secure in the QROM if every quantum polynomial-time adversary making $q$ superposition queries has negligible advantage. Classical random-oracle proof techniques that record queries, adaptively program answers or rewind the adversary do not transfer directly, since quantum queries cannot be copied or observed without disturbance.

## Depends on

- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [BQP](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Dan Boneh, Özgür Dagdelen, Marc Fischlin, Anja Lehmann, Christian Schaffner, Mark Zhandry, "Random Oracles in a Quantum World", ASIACRYPT (2011).
- Mark Zhandry, "How to Record Quantum Queries, and Applications to Quantum Indifferentiability", CRYPTO (2019), IACR ePrint 2018/276.
