# One-wayness from IND-CPA security for large message spaces

Let $\mathrm{PKE}$ have a finite message space $M$. In the OW-CPA experiment the adversary receives $pk$ and $\mathrm{Enc}(pk, m^*)$ for a uniform $m^*$ and must output $m^*$. For every OW-CPA adversary $\mathcal{A}$ there is an IND-CPA adversary $\mathcal{B}$ (which submits two independent uniform messages and outputs $1$ iff $\mathcal{A}$ returns the first) such that

$$
\mathrm{Adv}^{\mathrm{ow\text{-}cpa}}(\mathcal{A}) \le \mathrm{Adv}^{\mathrm{ind\text{-}cpa}}(\mathcal{B}) + \frac{1}{|M|}.
$$

## Proof sketch

When the challenge encrypts the second message, $\mathcal{A}$'s view is independent of the first, which it outputs with probability $1/|M|$.

## Depends on

- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](pke-with-explicit-coins.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
