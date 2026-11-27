# Shor's algorithm factors integers in quantum polynomial time

There are polynomials $a$ and $s$, a polynomial-time gate generator and a polynomial-time classical post-processing map such that the following holds for every integer $N > 1$. On the least-significant-bit-first binary expansion of $N$, the generator outputs a circuit of at most $s$ gates (as a function of the input length), each well formed on the input qubits plus $a$ ancilla qubits. Running the circuit on the standard input state for $N$ and measuring in the computational basis gives, with probability at least $2/3$, an outcome whose post-processed decoding is either a nontrivial factor $d$ of $N$ ($1 < d < N$ and $d \mid N$) or $0$ with $N$ prime.

The gate model is the polynomial-time uniform circuit model of BQP: 2-local unitary gates with rational entries.

## Sources

- P. W. Shor, Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer, SIAM J. Comput. 26 (1997), 1484–1509, Section 5; M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press, 2000, Section 5.3.
