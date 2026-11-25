# Conformance of finite-state machines and fault domains

A deterministic, completely specified Mealy machine over finite input and output alphabets $I$ and $O$ maps every input word $u \in I^*$ to an output word of the same length. An implementation machine $M'$ *conforms* to a specification $M$ when both produce the same output word from their initial states on every input word. For $m \ge 1$, the fault domain $\mathcal{D}_m$ is the set of deterministic, completely specified Mealy machines over $I$ and $O$ with at most $m$ states; a test suite is $m$-complete for $M$ when every machine in $\mathcal{D}_m$ that passes it conforms to $M$.

## Depends on

- [Mealy machine](../../../TheoryOfComputation/regular-languages/automata-and-expressions/sequential-transducers-mealy-and-moore-machines/mealy-machine.md)
- [Output word of a Mealy machine run](../../../TheoryOfComputation/regular-languages/automata-and-expressions/sequential-transducers-mealy-and-moore-machines/run-out-2.md)

## Sources

- J. Peleska, *Complete property-oriented testing with symbolic methods*, project report, University of Bremen, <https://www.informatik.uni-bremen.de/agbs/projects/cpotsm/cpotsm.pdf>
- Original method: T. S. Chow, "Testing software design modeled by finite-state machines", *IEEE Transactions on Software Engineering* SE-4(3):178–187, 1978. Peleska credits the W-method to Vasilevskii (1973) and Chow (1978).
