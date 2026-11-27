# Private quantum channels need $2n$ bits of key

A *private quantum channel* for $n$ qubits is a family of unitaries $U_1, \dots, U_N$ with probabilities $p_1, \dots, p_N$ such that $\sum_j p_j U_j \rho U_j^\dagger$ is the same state for every $n$-qubit state $\rho$. Every private quantum channel uses key entropy $H(p) \ge 2n$ bits (so $N \ge 4^n$), also when the unitaries act on the message together with ancilla qubits in a fixed state, and the quantum one-time pad (a uniformly random Pauli on each qubit) attains this, so it is optimal. A family that only has to hide a smaller set of states can use less key: tensor products of $n$ real-amplitude qubits, and in particular the $2^n$ classical basis states, are all mapped to the same state by a random $\sigma_0$ or $\sigma_2$ on each qubit ($n$ bits of key), and hiding the classical basis states already needs $H(p) \ge n$.

## Proof sketch

The $2n$ bound: apply the channel to one half of a maximally entangled state of $2n$ qubits: since the channel maps every operator $X$ to $\mathrm{tr}(X)\,I/2^n$, the output is $I/2^n \otimes I/2^n$, of von Neumann entropy $2n$, while a $p$-weighted mixture of $N$ unitary images of a pure state has entropy at most $H(p)$. A family that only has to hide products of complex-amplitude qubits, unlike the real-amplitude products above, already needs the full $2n$ bits: the operators $\rho_1 \otimes \cdots \otimes \rho_n$ with each $\rho_i$ a pure qubit state span all operators on $n$ qubits (pure qubit states span the $2 \times 2$ matrices), so a channel that maps every such product to the same state maps every operator $X$ to $\mathrm{tr}(X)$ times that state by linearity, hence hides all $n$-qubit states and needs $H(p) \ge 2n$.

## Depends on

- [The quantum one-time pad](quantum-one-time-pad.md)

## Sources

- Andris Ambainis, Michele Mosca, Alain Tapp and Ronald de Wolf, "Private Quantum Channels", 41st Annual Symposium on Foundations of Computer Science (FOCS 2000), 2000, Definition 3.1 (private quantum channels, with ancilla), Theorem 4.1 (the Pauli one-time pad hides all $n$-qubit states with $2n$ bits), Theorem 4.2 (products of real-amplitude qubits, and so classical basis states, with $n$ bits), Theorem 5.3 (hiding the classical basis states needs $H(p) \ge n$) and Corollary 5.4 (hiding all states needs $H(p) \ge 2n$, hence $N \ge 2^{2n}$).
