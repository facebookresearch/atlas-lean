# Degenerate codes and the quantum Hamming bound

Gottesman asked in 1997 whether there is a degenerate $[[n, k, 2t + 1]]$ code with

$$\sum_{j=0}^{t} 3^j \binom{n}{j} \;>\; 2^{n-k} .$$

The [quantum Hamming bound](quantum-hamming-bound.md) forbids this for codes
[nondegenerate](../distance-of-a-quantum-code/degenerate-quantum-code.md) for the errors of weight at most $t$; its
counting argument fails for degenerate codes, where distinct errors may act identically on the code. Gottesman also
showed that no degenerate stabilizer code correcting one or two errors violates the bound, and
reported that the linear programming bounds exclude violations on fewer than $30$ qubits. Dallas, Andreadakis and Lidar
(2022) showed that no qubit code of distance below $127$ violates it, degenerate or not. This page records the question as
it was posed and these published partial answers; it does not assert its present status.

## Depends on

- [The quantum Hamming bound](quantum-hamming-bound.md)
- [Degenerate quantum code](../distance-of-a-quantum-code/degenerate-quantum-code.md)

## Sources

- E. Dallas, F. Andreadakis and D. Lidar, *No $((n, K, d < 127))$ code can violate the quantum Hamming bound*, IEEE BITS the Information Theory Magazine 2 (2022), 33, arXiv:2208.11800, the main theorem (a combination of Rains's shadow bound and the Li–Xing linear-programming bound).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 7.1 ("It is unknown whether there are any degenerate codes that exceed the quantum Hamming bound") and Section 7.3.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.8.1.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2 ("we do not know of any codes that beat it").
