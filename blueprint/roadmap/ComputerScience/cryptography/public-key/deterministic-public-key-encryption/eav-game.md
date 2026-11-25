# Eavesdropping experiment for deterministic encryption

For a deterministic public-key encryption function $\mathrm{Enc}$, the eavesdropping experiment
$\mathrm{PubK}^{\mathrm{eav}}$ (Katz and Lindell, Section 11.2.1) draws a key pair from a
key-generation distribution, uniform coins and a uniform challenge bit $b$. The adversary sees the
public key $pk$ and submits an eligible pair $(m_0, m_1)$, the challenge is $\mathrm{Enc}_{pk}(m_b)$,
and the experiment outputs $1$ when the guess equals $b$. Encryption uses no randomness.
