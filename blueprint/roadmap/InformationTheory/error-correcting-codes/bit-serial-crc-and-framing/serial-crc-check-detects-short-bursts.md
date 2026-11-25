# A bit-serial CRC check detects every short burst

Let $g$ be a monic polynomial over $\mathbb F_2$ of degree $r \ge 1$ with $g(0) = 1$, and let a frame of $n$ bits carry the
CRC encoding $c$ of a message, read most significant bit first, so that its polynomial is $c$ and $g \mid c$. Feed the
received $n$ bits, without appended zeros, through the zero-initialized [bit-serial CRC register](serial-crc-register-computes-the-remainder.md)
of $g$ and accept the frame exactly when the final state is $0$. Then an error-free frame is accepted, and a frame received
as $c + e$, where $e \ne 0$ is a burst of length at most $r$ lying within the $n$ positions of the frame, is rejected.

By the register formula the final state is the received polynomial modulo $g$: it is $c \bmod g = 0$ for an error-free frame
and $(c + e) \bmod g = e \bmod g \ne 0$ otherwise, because $g$ is not divisible by $X$ and so divides no
[burst of length at most $\deg g$](../cyclic-redundancy-checks/not-dvd-of-is-burst-le.md). For example, the zero-initialized,
unreflected 16-bit check with $g = X^{16} + X^{12} + X^5 + 1$ detects every burst of length at most $16$.

## Depends on

- [A bit-serial CRC register computes the remainder](serial-crc-register-computes-the-remainder.md)
- [CRC encoder](../cyclic-redundancy-checks/encode.md)
- [CRC codewords are multiples of the generator](../cyclic-redundancy-checks/dvd-encode.md)
- [Burst errors](../cyclic-redundancy-checks/is-burst-le.md)

## Proof depends on

- [Short bursts are detected](../cyclic-redundancy-checks/not-dvd-of-is-burst-le.md)

## Sources

- W. W. Peterson and D. T. Brown, "Cyclic codes for error detection", *Proceedings of the IRE* 49(1):228–235, 1961.
- S. Lin and D. J. Costello, *Error Control Coding*, 2nd edition, Pearson Prentice Hall, 2004, Chapter 5 (cyclic codes and their shift-register encoders).
