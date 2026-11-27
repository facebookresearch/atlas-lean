# Bernstein–Vazirani algorithm

If $f(x) = s\cdot x + b$ for all $x \in \mathbb{Z}_2^n$, then one query of Fourier sampling produces
exactly the state $(-1)^b |s\rangle$, so measuring it returns the hidden string $s$ with certainty. In coordinates, for bitstrings $s, t$ and a bit $\beta$ with $f(x) = s \cdot x \oplus \beta$, the normalized sum $2^{-n} \sum_x (-1)^{t \cdot x} (-1)^{f(x)}$ is $(-1)^\beta$ when $t = s$ and $0$ otherwise.

Bernstein and Vazirani (Section 8.4) state the parity problem with $b = 0$ and an oracle that computes
$f$ into a register, which their algorithm calls twice (compute, then uncompute); the version here, with
one call to the phase oracle and the extra constant $b$, is the one of Cleve, Ekert, Macchiavello and
Mosca (equations (3.7)–(3.9)). The phase oracle is what one call to the reversible oracle does to a
target qubit in $|0\rangle - |1\rangle$ ([Phase kickback](phase-kickback.md)).

## Informally uses

- [Amplitudes of Fourier sampling](fourier-sample-apply.md): the amplitude of $|t\rangle$ becomes $2^{-n}(-1)^b\sum_x (-1)^{(s+t)\cdot x}$.
- [Orthogonality of the parity characters](sum-sign-of-bit-bit-dot.md): that sum is $2^n$ when $t = s$ and $0$ otherwise.

## Background

- [Classical evaluations: fewer than $n$ never determine $s$](exists-ne-zero-forall-bit-dot-eq-zero.md): the classical counterpart, which needs $n$ evaluations.

## Sources

- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997 (https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf), Section 8.4. Theorem numbers on this page refer to that version.
- R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, "Quantum algorithms revisited", Proceedings of the Royal Society of London A 454 (1998), 339–354; arXiv:quant-ph/9708016v1, Section 3, equations (3.1)–(3.9).
