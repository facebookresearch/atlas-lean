# The derandomizing transform $T$

Let $\mathrm{PKE} = (\mathrm{Gen}, \mathrm{Enc}, \mathrm{Dec})$ have explicit coins in $R$, and let $G : M \to R$ be a hash function (a random oracle). The transform $T$ yields the deterministic scheme $\mathrm{PKE}_1 = T[\mathrm{PKE}, G]$ with

$$
\mathrm{Enc}_1(pk, m) = \mathrm{Enc}(pk, m; G(m)), \qquad \mathrm{Dec}_1(sk, c) = \begin{cases} m' & \text{if } m' = \mathrm{Dec}(sk, c) \ne \bot \text{ and } \mathrm{Enc}(pk, m'; G(m')) = c,\\ \bot & \text{otherwise.}\end{cases}
$$

$T$ is *rigid*: every plaintext $m'$ accepted by $\mathrm{Dec}_1$ re-encrypts exactly to $c$ and satisfies $\mathrm{Dec}(sk, c) = m'$.

## Depends on

- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](pke-with-explicit-coins.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
