# The reduction from Goldwasser–Micali to the residuosity experiment

From an eavesdropper $A$ against the [one-bit scheme](scheme.md): on the public key $y$, a challenge
$z$ and coins $r$, let $(m_0, m_1)$ be the two messages $A$ chooses. If $m_0 = m_1$, output $0$.
Otherwise give $A$ the ciphertext $z$ if $m_0 = 0$ and $y z$ if $m_0 = 1$, and output its guess. A
square $z = x^2$ is then an encryption of $m_0$, and $z = y x^2$ an encryption of $m_1$ (for
$m_0 = 1$ because $y \cdot y x^2 = (y x)^2$ and $y x$ is uniform when $x$ is).
