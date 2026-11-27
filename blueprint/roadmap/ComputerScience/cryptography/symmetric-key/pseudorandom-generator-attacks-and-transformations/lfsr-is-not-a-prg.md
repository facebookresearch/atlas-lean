# No linear feedback shift register is a pseudorandom generator

For an $n$-bit LFSR with tap set $T$ and output length $\ell \ge n + 1$, any $n$ consecutive output bits determine all later output bits by the linear recurrence. Hence the test that checks whether $y_{n+1} = \bigoplus_{v\in T} y_{1+v}$ (with the taps known) accepts every generator output and a uniform string with probability $1/2$, giving advantage $1/2$. If the taps are part of the seed and $\ell \ge 2n + 1$, then any $2n$ consecutive output bits determine all later output bits: Berlekamp–Massey returns a shortest linear recurrence consistent with them, which has length at most $n$ and generates the rest of the sequence (it need not recover the taps). So the efficient test comparing bit $2n + 1$ with this prediction accepts every generator output and a uniform string with probability $1/2$, again giving advantage $1/2$; hence no LFSR with known taps and $\ell \ge n + 1$, and no LFSR family with taps in the seed and $\ell \ge 2n + 1$, is a pseudorandom generator.

## Proof sketch

The state after $n$ steps consists of the last $n$ outputs, so the next output is the stated XOR. For taps in the seed, let Berlekamp–Massey return a recurrence of length $L \le n$ valid on the first $N \ge 2n$ bits. If it failed at bit $N + 1$, Massey's length-change lemma would force every recurrence valid through bit $N + 1$ to have length at least $N + 1 - L \ge n + 1$, contradicting the true recurrence of length $n$; by induction it predicts every later bit.

## Depends on

- [Linear feedback shift register](linear-feedback-shift-register.md)
- [Asymptotic PRG security relative to a class of distinguishers](../pseudorandom-generators/prgsecure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. L. Massey, "Shift-Register Synthesis and BCH Decoding", IEEE Transactions on Information Theory 15(1), 1969.
