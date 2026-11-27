# Leverrier-Zemor: efficient decoding up to a constant fraction of the length

For the asymptotically good quantum Tanner codes there is a constant $c > 0$ and a decoder running in linear time (sequentially), or in logarithmic depth in parallel, that corrects every adversarial Pauli error of weight at most $c n$: given the syndrome of an error $e$ with $|e| \le cn$, it outputs $\hat e$ with $\hat e e$ a stabilizer.

## Proof sketch

The decoder is a local-improvement (small-set-flip) procedure: at each vertex, it looks for a local codeword of $C_A \otimes C_B$ (respectively the dual tensor code) whose addition decreases the syndrome weight by a constant fraction of its size. Product-expansion and spectral expansion guarantee that whenever the error is small but nonzero modulo stabilizers, such an improving local move exists, so the syndrome weight decreases geometrically.

## Depends on

- [Leverrier-Zemor: quantum Tanner codes are asymptotically good](quantum-tanner-codes-have-linear-distance.md)
- [Quantum Tanner codes](quantum-tanner-codes.md)

## Sources

- Anthony Leverrier, Gilles Zemor, "Efficient decoding up to a constant fraction of the code length for asymptotically good quantum codes", SODA (2023); arXiv:2206.07571.
