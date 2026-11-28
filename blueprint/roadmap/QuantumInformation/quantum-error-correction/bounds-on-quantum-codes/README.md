# Bounds on quantum codes

How many qubits a code of given distance can encode is bounded above by the quantum Hamming bound, which the counting
argument proves for nondegenerate codes, and by the quantum Singleton bound, which holds for all codes; the quantum Gilbert–Varshamov bound
and Calderbank and Shor's construction show that codes with positive rate and positive relative distance exist. Whether
degenerate codes can beat the quantum Hamming bound was posed as a question in 1997; published work has since excluded
violations for qubit codes of distance below $127$. For erasures, four qubits are needed to protect one qubit.

- [The quantum Hamming bound](quantum-hamming-bound.md)
- [The quantum Gilbert–Varshamov bound](quantum-gilbert-varshamov-bound.md)
- [Good CSS codes exist](good-css-codes-exist.md)
- [Degenerate codes and the quantum Hamming bound](degenerate-codes-and-the-quantum-hamming-bound.md)
- [Four qubits are needed to correct one erasure](four-qubits-are-needed-to-correct-one-erasure.md)
- [The quantum MacWilliams identity](quantum-macwilliams-identity.md)
- [The greedy Gilbert–Varshamov lemma for code families](greedy-gilbert-varshamov-lemma-for-code-families.md)
- [Counting weakly self-dual codes](counting-weakly-self-dual-codes.md)

## Related topics

- [The quantum Singleton bound](../distance-of-a-quantum-code/quantum-singleton-bound.md): the bound $n - k \ge 2(d - 1)$, valid for degenerate codes too.
- [Bounds on code size](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/README.md): the classical Hamming, Singleton and Gilbert–Varshamov bounds.

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Chapter 7.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Sections 7.8 and 7.14.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2.
