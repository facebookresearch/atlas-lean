# Leftover hash lemma with side information

Let $H : K \times S \to T$ be a keyed hash function with $K$, $S$, $T$ finite and $N = |T|$, and suppose $H$ is a $(1+\alpha)/N$-universal hash function for
some $\alpha \ge 0$. Let $(s, z)$ be a pair of random variables, a secret $s$ in $S$ and side information $z$ with finitely many values, and let the key $k$
be uniform on $K$ and independent of $(s, z)$. For each value $z_0$ with $\Pr[z = z_0] > 0$ let $\gamma(z_0) = \max_x \Pr[s = x \mid z = z_0]$, and let $\delta$
be the statistical distance between $(k, z, H(k, s))$ and $(k, z, t)$ with $t$ uniform on $T$ and independent of $(k, z)$.

- (*Worst-case form.*) If $\gamma(z_0) \le \gamma$ for every $z_0$ with $\Pr[z = z_0] > 0$, then $\delta \le \tfrac12\sqrt{N\gamma + \alpha}$.
- (*Average-case form.*) With $\gamma_{\mathrm{avg}} = \sum_{z_0} \Pr[z = z_0]\,\gamma(z_0)$, $\delta \le \tfrac12\sqrt{N\gamma_{\mathrm{avg}} + \alpha}$.
- (*Several sources.*) If $(s_1, z_1), \dots, (s_m, z_m)$ are mutually independent and independent of $k$, and every $\gamma_i(z_0) \le \gamma$, then the statistical
  distance between $(k, z_1, \dots, z_m, H(k, s_1), \dots, H(k, s_m))$ and $(k, z_1, \dots, z_m, t_1, \dots, t_m)$ with $t_1, \dots, t_m$ uniform and independent is at
  most $\tfrac m2\sqrt{N\gamma + \alpha}$.

Proof. Since $z$ has the same law in both distributions, $\delta = \sum_{z_0}\Pr[z = z_0]\,\delta(z_0)$, where $\delta(z_0)$ is the distance after conditioning on
$z = z_0$. Conditioned on $z = z_0$, $k$ is still uniform and independent of $s$, and $s$ has guessing probability $\gamma(z_0)$, so the leftover hash lemma
with $m = 1$ gives $\delta(z_0) \le \tfrac12\sqrt{N\gamma(z_0) + \alpha}$. This gives the worst-case form, and the average-case form follows by concavity of the
square root (Jensen's inequality). For several sources, conditioning on $(z_1, \dots, z_m)$ leaves $k, s_1, \dots, s_m$ mutually independent, and the leftover
hash lemma with $m$ sources applies to each conditional law.

## Depends on

- [Conditional guessing probability and min-entropy](conditional-guessing-probability-and-min-entropy.md)
- [Bounded universal hash functions](../hash-functions/bounded-universal-hash-functions.md)

## Proof depends on

- [Leftover hash lemma](leftover-hash-lemma.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>: Theorem 8.11 and the discussion following it of a secret $s$ with side information $I(s)$, independent of the key, and the bound on distinguishing $(k, I(s), H(k, s))$ from $(k, I(s), t)$. The conditioning argument and the average-case form are derived on this page.
