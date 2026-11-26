# IKNP oblivious-transfer extension

Let $\kappa$ be a security parameter, $m = \mathrm{poly}(\kappa)$, and $H$ a correlation-robust hash family. The IKNP protocol implements $m$ transfers of strings from $\kappa$ base transfers of $m$-bit strings in the reverse direction: the sender picks $s \in \{0,1\}^\kappa$, the receiver with choice vector $r \in \{0,1\}^m$ picks a random matrix $T \in \{0,1\}^{m\times\kappa}$ and acts as base-OT sender with column pairs $(t^i, t^i \oplus r)$; the sender, as base-OT receiver with choice $s_i$, obtains the matrix $Q$ with columns $q^i = t^i \oplus s_i r$, so that its $j$-th row is $q_j = t_j \oplus r_j s$. The sender sends $y_j^0 = x_j^0 \oplus H(j, q_j)$ and $y_j^1 = x_j^1 \oplus H(j, q_j \oplus s)$, and the receiver outputs $y_j^{r_j} \oplus H(j, t_j)$. Then: (i) the receiver outputs $x_j^{r_j}$ for all $j$; (ii) the protocol is perfectly private against the sender (in the base-OT hybrid model), since the columns $t^i \oplus s_i r$ are uniform whatever $r$; (iii) it is semi-honest secure against the receiver if $H$ is correlation robust, i.e. $(H(j, t_j \oplus s))_j$ is pseudorandom given $(t_j)_j$ for uniform secret $s$. Hence, for polynomially many extended transfers, the protocol family is semi-honest secure.

## Proof sketch

The key identity is $q_j = t_j \oplus r_j s$, so the sender's two masks are $H(j, t_j)$ on the receiver's side and $H(j, t_j \oplus s)$ on the other; the latter is pseudorandom to the receiver, which does not know $s$.

## Depends on

- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](oblivious-transfer-functionalities.md)
- [Correlation-robust hash functions](correlation-robust-hash.md)
- [Two-party security against semi-honest adversaries](../two-party-security-against-semi-honest.md)

## Sources

- Yuval Ishai, Joe Kilian, Kobbi Nissim and Erez Petrank, "Extending Oblivious Transfers Efficiently", Advances in Cryptology – CRYPTO 2003, 2003.
