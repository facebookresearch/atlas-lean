# The CPA experiment with a given keystream

For a chosen-plaintext adversary against the stream cipher, a keystream $y$, a challenge bit $b$ and
coins $r$, the deterministic run answers every encryption query $m$ with $y + m$, gives the challenge
$y + m_b$, and returns the adversary's guess.
