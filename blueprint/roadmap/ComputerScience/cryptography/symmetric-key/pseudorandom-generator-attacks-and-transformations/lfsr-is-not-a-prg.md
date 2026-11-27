# No linear feedback shift register is a pseudorandom generator

For an $n$-bit LFSR with tap set $T$ and output length $\ell \ge n + 1$, any $n$ consecutive output bits determine all later output bits by the linear recurrence. Hence the test that checks whether $y_{n+1} = \bigoplus_{v\in T} y_{1+v}$ (with the taps known) accepts every generator output and a uniform string with probability $1/2$, giving advantage $1/2$. Even with unknown taps, $2n$ output bits determine the taps by solving a linear system (Berlekamp–Massey), so no family of LFSRs is a pseudorandom generator.

## Proof sketch

The state after $n$ steps consists of the last $n$ outputs, so the next output is the stated XOR. For unknown taps, $2n$ consecutive outputs give $n$ linear equations in the tap indicators whose matrix is invertible for a maximal-length register, or Berlekamp–Massey finds the shortest recurrence in general.

## Depends on

- [Linear feedback shift register](linear-feedback-shift-register.md)
- [Asymptotic PRG security relative to a class of distinguishers](../pseudorandom-generators/prgsecure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. L. Massey, "Shift-Register Synthesis and BCH Decoding", IEEE Transactions on Information Theory 15(1), 1969.
