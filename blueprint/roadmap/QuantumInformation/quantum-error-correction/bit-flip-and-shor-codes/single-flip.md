# Single bit flips on three qubits

The errors corrected by the bit-flip code are indexed by $\{\varnothing, 1, 2, 3\}$: $\varnothing$ stands
for no error, with flip pattern $0 \in \mathbb{F}_2^3$, and $i$ for a bit flip on qubit $i$, with flip pattern
the unit vector $e_i$. The corresponding operator is the Pauli operator $X^{e} = X^{e} Z^{0}$ of
[CSS codes](../css-codes/pauli.md), so the error set is $\{I, X_1, X_2, X_3\}$.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.1.
