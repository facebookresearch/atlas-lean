# Degenerate codes and the quantum Hamming bound

Open problem: is there a degenerate $[[n, k, 2t + 1]]$ code with

$$\sum_{j=0}^{t} 3^j \binom{n}{j} \;>\; 2^{n-k} \,?$$

The [quantum Hamming bound](quantum-hamming-bound.md) forbids this for codes
[nondegenerate](../distance-of-a-quantum-code/degenerate-quantum-code.md) for the errors of weight at most $t$; its
counting argument fails for degenerate codes, where distinct errors may act identically on the code. Gottesman shows that
no degenerate stabilizer code correcting one or two errors violates the bound, and reports that the linear programming
bounds exclude violations on fewer than $30$ qubits; Gottesman and Preskill both record the general question as open.

## Depends on

- [The quantum Hamming bound](quantum-hamming-bound.md)
- [Degenerate quantum code](../distance-of-a-quantum-code/degenerate-quantum-code.md)

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 7.1 ("It is unknown whether there are any degenerate codes that exceed the quantum Hamming bound") and Section 7.3.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.8.1.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2 ("we do not know of any codes that beat it").
