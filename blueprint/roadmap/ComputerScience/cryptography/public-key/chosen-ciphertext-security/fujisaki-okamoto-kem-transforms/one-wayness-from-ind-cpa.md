# One-wayness from IND-CPA security for large message spaces

Let $\mathrm{PKE}$ have a finite message space $M$. In the OW-CPA experiment the adversary receives $pk$ and $\mathrm{Enc}(pk, m^*)$ for a uniform $m^*$ and must output $m^*$; $\mathrm{PKE}$ is *one-way* if every efficient adversary wins with negligible probability. If $\mathrm{PKE}$ is IND-CPA secure (semantically secure, as in the linked CPA experiment) and $|M|$ is super-polynomial in the security parameter, then $\mathrm{PKE}$ is one-way (Boneh and Shoup, Exercise 12.9, with one-wayness as in their Definition 12.5).

## Proof sketch

The following explicit reduction and bound are derived here. For every OW-CPA adversary $\mathcal{A}$ let $\mathcal{B}$ be the IND-CPA adversary with the same running time as $\mathcal{A}$ up to sampling two messages that submits two independent uniform messages $m_0, m_1$, runs $\mathcal{A}$ on the challenge, and guesses $b' = 0$ iff $\mathcal{A}$ returns $m_0$. When the challenge encrypts $m_0$, $\mathcal{B}$ guesses $0$ with probability $\mathrm{Adv}^{\mathrm{ow\text{-}cpa}}(\mathcal{A})$; when it encrypts $m_1$, $\mathcal{A}$'s view is independent of $m_0$, which it outputs with probability exactly $1/|M|$. Hence $\Pr[b' = b] - 1/2 = \tfrac12\bigl(\mathrm{Adv}^{\mathrm{ow\text{-}cpa}}(\mathcal{A}) - 1/|M|\bigr)$, that is,

$$
\mathrm{Adv}^{\mathrm{ow\text{-}cpa}}(\mathcal{A}) \le 2\,\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}(\mathcal{B}) + \frac{1}{|M|}
$$

for the guessing advantage $\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}(\mathcal{B}) = |\Pr[b' = b] - 1/2|$ of the linked CPA experiment and of Hofheinz, Hövelmanns and Kiltz's Definition 2.2, and the factor $2$ disappears for the distinguishing advantage $|\Pr[b' = 1 \mid b = 1] - \Pr[b' = 1 \mid b = 0]|$, which is twice the guessing advantage. Both terms are negligible under the hypotheses. Hofheinz, Hövelmanns and Kiltz's Lemma 2.3 states the bound without the factor $2$ for the guessing advantage, which is false: for $\mathrm{Enc}(pk, m) = m$ and $|M| \ge 3$ the inverter that returns the ciphertext has OW-CPA advantage $1$, while every guessing advantage is at most $1/2$.

## Depends on

- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](pke-with-explicit-coins.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)
- [One-way and unpredictable public-key encryption](../../elgamal-encryption/elgamal-variants-and-properties/one-way-and-unpredictable-pke.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023, Definition 12.5 and Exercise 12.9.
- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017, Definition 2.2 and Lemma 2.3.
