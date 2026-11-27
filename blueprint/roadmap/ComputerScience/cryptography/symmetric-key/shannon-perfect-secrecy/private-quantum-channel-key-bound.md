# Private quantum channels need $2n$ bits of key

A *private quantum channel* for $n$ qubits is a family of unitaries $U_1, \dots, U_N$ with probabilities $p_1, \dots, p_N$ such that $\sum_j p_j U_j \rho U_j^\dagger$ is the same state for every $n$-qubit state $\rho$. Every private quantum channel that hides all $n$-qubit states uses key entropy $H(p) \ge 2n$ bits (so $N \ge 4^n$), hence the quantum one-time pad is optimal. If the channel only needs to hide unentangled (product) states, it already must hide all states: its average annihilates every off-diagonal operator $|x\rangle\langle y|$ with $x \ne y$, and a Bell-basis reduction shows it hides all states; for classical basis messages alone, $n$ bits of key suffice and are necessary.

## Proof sketch

Apply the channel to one half of a maximally entangled state of $2n$ qubits: since the channel maps every operator $X$ to $\mathrm{tr}(X)\,I/2^n$, the output is $I/2^n \otimes I/2^n$, of von Neumann entropy $2n$, while a $p$-weighted mixture of $N$ unitary images of a pure state has entropy at most $H(p)$.

## Depends on

- [The quantum one-time pad](quantum-one-time-pad.md)

## Sources

- Andris Ambainis, Michele Mosca, Alain Tapp and Ronald de Wolf, "Private Quantum Channels", 41st Annual Symposium on Foundations of Computer Science (FOCS 2000), 2000.
