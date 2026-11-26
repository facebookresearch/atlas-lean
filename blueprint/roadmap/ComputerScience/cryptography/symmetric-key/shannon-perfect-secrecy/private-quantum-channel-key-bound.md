# Private quantum channels need $2n$ bits of key

A *private quantum channel* for $n$ qubits is a family of unitaries $U_1, \dots, U_N$ with probabilities $p_1, \dots, p_N$ such that $\sum_j p_j U_j \rho U_j^\dagger$ is the same state for every $n$-qubit state $\rho$. Every private quantum channel that hides all $n$-qubit states uses key entropy $H(p) \ge 2n$ bits (so $N \ge 4^n$), hence the quantum one-time pad is optimal. If the channel only needs to hide unentangled (product) states, it already must hide all states: its average annihilates every off-diagonal operator $|x\rangle\langle y|$ with $x \ne y$, and a Bell-basis reduction shows it hides all states; for classical basis messages alone, $n$ bits of key suffice and are necessary.

## Proof sketch

Apply the channel to one half of a maximally entangled state of $2n$ qubits: the output must be a fixed state tensored with nothing correlated, and its von Neumann entropy, which is at most $H(p)$ plus the entropy of the half, must be $2n$.

## Depends on

- [The quantum one-time pad](quantum-one-time-pad.md)

## Sources

- Andris Ambainis, Michele Mosca, Alain Tapp and Ronald de Wolf, "Private Quantum Channels", 41st Annual Symposium on Foundations of Computer Science (FOCS 2000), 2000.
