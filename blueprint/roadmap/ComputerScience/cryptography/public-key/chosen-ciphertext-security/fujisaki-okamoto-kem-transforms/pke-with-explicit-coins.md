# Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness

A *public-key encryption scheme with explicit coins* is a triple $(\mathrm{Gen}, \mathrm{Enc}, \mathrm{Dec})$ where $\mathrm{Enc}(pk, m; r)$ is a deterministic function of the public key, the message $m \in M$ and coins $r$ drawn uniformly from a finite set $R$, and $\mathrm{Dec}(sk, c) \in M \cup \{\bot\}$. It is *$\delta$-correct* if

$$
\mathbb{E}_{(pk, sk) \leftarrow \mathrm{Gen}}\Bigl[\max_{m \in M} \Pr_{r \leftarrow R}\bigl[\mathrm{Dec}(sk, \mathrm{Enc}(pk, m; r)) \ne m\bigr]\Bigr] \le \delta ,
$$

and *$\gamma$-spread* if for every key pair, message $m$ and ciphertext $c$, $\Pr_{r}[\mathrm{Enc}(pk, m; r) = c] \le 2^{-\gamma}$. IND-CPA security is defined by the usual two-stage left-or-right experiment.

## Depends on

- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
