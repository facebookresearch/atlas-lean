# Characterizations of perfect security

Let $(E, D)$ be a Shannon cipher over finite key, message and ciphertext spaces $(K, M, C)$ with $K$ nonempty and a uniformly random key, and say it is *perfectly secure* if the ciphertext distribution $E(k, m)$ is the same for all messages $m$. The following are equivalent: (i) perfect security; (ii) for all $m, m'$ and $c$, the number of keys $k$ with $E(k, m) = c$ equals the number with $E(k, m') = c$; (iii) for every event (predicate) $\phi$ on ciphertexts and all $m, m'$, $\Pr[\phi(E(k, m))] = \Pr[\phi(E(k, m'))]$; (iv) for every distribution of the message $\mathbf{m}$ independent of the key, $\mathbf{m}$ and $\mathbf{c} = E(k, \mathbf{m})$ are independent, i.e. their joint law is the product of the marginals. A cipher in which every message and ciphertext are related by exactly one key is perfectly secure.

## Proof sketch

Under a uniform key, $\Pr[E(k, m) = c]$ is the number of such keys divided by $|K|$, giving (i)$\Leftrightarrow$(ii). (iii) is (i) applied to events, and (iv) follows by conditioning on $\mathbf{m}$; conversely, independence with a message law of full support gives equal conditional ciphertext laws.

## Depends on

- [The group one-time pad is perfectly secret](../one-time-pad-over-a-finite-group/group-otp-perfectly-secret.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
