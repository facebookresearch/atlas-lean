# Linear feedback shift register

An $n$-bit *linear feedback shift register* (LFSR) with tap set $T \subseteq \{0, \dots, n-1\}$ has state $(b_{n-1}, \dots, b_0) \in \{0,1\}^n$. Each clock cycle it outputs $b_0$, computes the feedback bit $b = \bigoplus_{v \in T} b_v$, and moves to the state $(b, b_{n-1}, \dots, b_1)$. As a generator it maps the initial state (the seed) to the first $\ell$ output bits; the output sequence satisfies the linear recurrence $y_{i+n} = \bigoplus_{v \in T} y_{i+v}$.

## Depends on

- [PRG advantage](../pseudorandom-generators/prg-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. L. Massey, "Shift-Register Synthesis and BCH Decoding", IEEE Transactions on Information Theory 15(1), 1969.
