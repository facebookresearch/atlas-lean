# The challenge is a one-time pad on a fresh counter range

Let $Y$ be an additive commutative group and $\ell \le N$. Let $\rho \in (\mathbb{Z}/N)^q$ and $r_s$ be such that the challenge counter range $r_s, \dots, r_s + \ell - 1$ is [fresh](ctr-fresh.md) for the query counters $\rho \in (\mathbb{Z}/N)^q$, let $f \colon \mathbb{Z}/N \to Y$, $b$ a bit and $c$ a first-phase computation of a CPA adversary. Let $(m_0, m_1)$ be the [challenge pair](ctr-msgs.md) that $c$ outputs when run on the tape $\rho$ with keyed function $f$ (zero if it is stopped), and put

$$
v = m_b - m_{\lnot b}.
$$

Then the [fixed-tape guess](../../security-games/generic-security-games/cpa-tape-guess.md) with the shifted function and the flipped bit equals the original one:

$$
\mathrm{guess}(\mathrm{ctrEncrypt}(\mathrm{ctrShift}(f, r_s, v), \cdot, \cdot), c, q, \rho, r_s, \lnot b) = \mathrm{guess}(\mathrm{ctrEncrypt}(f, \cdot, \cdot), c, q, \rho, r_s, b).
$$

The sign of $v$ matters: reversing it can change the challenge ciphertext, for example over $\mathbb{Z}/3$. No hypothesis $N \ne 0$ is needed.
