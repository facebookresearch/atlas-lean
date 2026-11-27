# Oblivious transfer of masked values from oblivious transfer of pads

Let the sender hold $(m_0, m_1) \in M^2$. In the hybrid model with an ideal 1-out-of-2 transfer of pads $(r_0, r_1)$ from a pad space, the *masked transfer* runs one pad transfer and then sends $(\mathrm{mask}(r_0, m_0), \mathrm{mask}(r_1, m_1))$; the receiver unmasks the chosen one. If unmasking with $r_c$ recovers $m_c$, the protocol is correct and perfectly private against a corrupted sender. Against a corrupted receiver its ideal game is the pad test: privacy holds exactly to the extent that $\mathrm{mask}(r_{1-c}, m_{1-c})$ hides $m_{1-c}$ given $r_c$. Instantiating pads with the DDH transfer of group elements and $\mathrm{mask}(r, m) = \mathrm{KDF}(r) \oplus m$ for a key-derivation function gives an OT of strings, secure for a corrupted receiver when $\mathrm{KDF}$ applied to the unchosen pad is pseudorandom.

## Proof sketch

The sender's view contains only its own pads, which a simulator samples. For the receiver, the second message is a deterministic function of the chosen output and of $\mathrm{mask}(r_{1-c}, m_{1-c})$, so the real and ideal games differ exactly in the pad test.

## Depends on

- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](oblivious-transfer-functionalities.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
