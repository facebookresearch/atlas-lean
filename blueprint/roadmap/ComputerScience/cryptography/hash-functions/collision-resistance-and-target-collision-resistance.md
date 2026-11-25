# Collision resistance and target collision resistance

Let $H$ be a hash function defined over $(M, T)$, where formally $H$ is indexed by a security parameter and a system parameter, so that an
efficient adversary must find collisions as a function of the system parameter. In the *collision-resistance game* the adversary outputs
$m_0, m_1 \in M$ and wins if $m_0 \ne m_1$ and $H(m_0) = H(m_1)$; its advantage $\mathrm{CRadv}[A, H]$ is the probability that it wins. $H$ is
*collision resistant* if $\mathrm{CRadv}[A, H]$ is negligible for every efficient adversary $A$.

Let $H$ be a keyed hash function defined over $(K, M, T)$. In the *target-collision-resistance game* the adversary first sends $m_0 \in M$, the
challenger then picks $k \in K$ uniformly at random and sends it to the adversary, and the adversary sends $m_1 \in M$; it wins if $m_0 \ne m_1$
and $H(k, m_0) = H(k, m_1)$, and $\mathrm{TCRadv}[A, H]$ is the probability that it wins. $H$ is *target collision resistant* if
$\mathrm{TCRadv}[A, H]$ is negligible for every efficient adversary $A$.

A collision-resistant hash function over $(M, T)$ is target collision resistant when viewed as a keyed hash function over $(K, M, T)$ with a key
space $K$ of size one.

## Depends on

- [Winning probability of a game](../security-games/games-and-advantages/win-prob.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>: Attack Game 8.1 and Definition 8.1 (collision resistance, with Section 8.1.1 on system parameters), and Attack Game 8.5 and Definition 8.7 with the remark following it (target collision resistance, and collision resistance as the one-key case).
