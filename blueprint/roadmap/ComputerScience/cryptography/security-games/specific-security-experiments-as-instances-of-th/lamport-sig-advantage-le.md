# Lamport one-time signature security bound

Let $X$ be finite and nonempty, $Y$ a type with decidable equality, $f \colon X \to Y$, $R$ finite and nonempty, and $\ell \ne 0$. Let $A = (\mathrm{choose}, \mathrm{forge})$ be a Lamport one-time forger with coins in $R$, and let $A'$ be its [embedding as a signature forger](to-sig-forger.md): the embedded signature forger draws its coins $r$ uniformly from $R$; on public key $pk$ it makes one signing query, on the message $\mathrm{choose}(pk, r)$, and on the answer $\sigma$ outputs $\mathrm{forge}(pk, \sigma, r)$ with the same coins $r$. Then

$$
\mathrm{Adv}^{\mathrm{sig}}(\mathrm{lamport}_f, A') \le 2\ell \cdot \Pr[\mathrm{invertGame}_f(\mathrm{invert}_f(A)) = \mathrm{true}],
$$

where the left side is the probability that the signature-forgery game of the [Lamport scheme](lamport.md) against $A'$ outputs true, and $\mathrm{invert}_f(A)$ is the inverter built from the original one-time forger $A$: given $y$, with a uniform position $(i, c)$, secret key and coins, it plants $y$ at position $(i, c)$ of the public key and returns the $i$th forged signature entry when $A$'s requested message has $m_i \ne c$ and its forged message has $m'_i = c$, and fails otherwise. The one-wayness game draws $x$ uniformly from $X$ and succeeds when the inverter outputs some $x'$ with $f(x') = f(x)$ (Katz and Lindell, Theorem 12.16).

The bound concerns this particular embedded one-query forger, not every forger with signing-oracle access.
