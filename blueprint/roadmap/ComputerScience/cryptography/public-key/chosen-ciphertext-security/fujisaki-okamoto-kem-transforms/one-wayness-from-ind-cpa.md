# One-wayness from IND-CPA security for large message spaces

Let $\mathrm{PKE}$ have a finite message space $M$. In the OW-CPA experiment the adversary receives $pk$ and $\mathrm{Enc}(pk, m^*)$ for a uniform $m^*$ and must output $m^*$. For every OW-CPA adversary $\mathcal{A}$ there is an IND-CPA adversary $\mathcal{B}$ with the same running time as $\mathcal{A}$ up to sampling two messages (it submits two independent uniform messages $m_0, m_1$, runs $\mathcal{A}$ on the challenge, and guesses $b' = 0$ iff $\mathcal{A}$ returns $m_0$) such that

$$
\mathrm{Adv}^{\mathrm{ow\text{-}cpa}}(\mathcal{A}) \le 2\,\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}(\mathcal{B}) + \frac{1}{|M|},
$$

where $\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}(\mathcal{B}) = |\Pr[b' = b] - 1/2|$ is the guessing advantage, as in the linked CPA experiment and in Hofheinz, Hövelmanns and Kiltz's Definition 2.2. For the distinguishing advantage $|\Pr[b' = 1 \mid b = 1] - \Pr[b' = 1 \mid b = 0]|$, which is twice the guessing advantage, the factor $2$ disappears. Their Lemma 2.3 states the bound without the factor $2$ for the guessing advantage, which is false: for $\mathrm{Enc}(pk, m) = m$ and $|M| \ge 3$ the inverter that returns the ciphertext has OW-CPA advantage $1$, while every guessing advantage is at most $1/2$.

## Proof sketch

When the challenge encrypts $m_0$, $\mathcal{B}$ guesses $0$ with probability $\mathrm{Adv}^{\mathrm{ow\text{-}cpa}}(\mathcal{A})$; when it encrypts $m_1$, $\mathcal{A}$'s view is independent of $m_0$, which it outputs with probability exactly $1/|M|$. Hence $\Pr[b' = b] - 1/2 = \tfrac12\bigl(\mathrm{Adv}^{\mathrm{ow\text{-}cpa}}(\mathcal{A}) - 1/|M|\bigr)$.

## Depends on

- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](pke-with-explicit-coins.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017, Definition 2.2 and Lemma 2.3.
