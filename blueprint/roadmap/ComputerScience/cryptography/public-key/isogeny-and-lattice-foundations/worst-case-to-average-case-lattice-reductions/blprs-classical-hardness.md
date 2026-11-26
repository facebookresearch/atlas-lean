# Classical hardness of LWE with polynomial modulus

There is a classical polynomial-time reduction from $\mathrm{GapSVP}_\gamma$ in dimension $\sqrt{n}$ (for $\gamma$ polynomial in $n$) to decision LWE in dimension $n$ with a polynomial modulus $q$ and Gaussian error rate $\alpha$ such that $\gamma=\widetilde{O}(n^{2}/\alpha)$ up to polynomial factors. The key ingredients are a modulus-switching reduction from LWE with modulus $q$ in dimension $n$ to LWE with modulus $q'$ in dimension $n\log q/\log q'$ (with a small increase in error), and the classical reduction for exponential moduli.

## Proof sketch

Apply Peikert's classical reduction with exponential modulus in dimension $\sqrt{n}$. Then trade modulus for dimension: LWE with secret in dimension $k$ and modulus $q^{k'}$ reduces to LWE in dimension $kk'$ with modulus $q$, via a gadget decomposition of secrets combined with LWE with binary secrets (shown hard by an entropic leftover-hash argument). Error growth is controlled by modulus switching with rounding.

## Depends on

- [Peikert's classical reduction from GapSVP to LWE with exponential modulus](peikert-classical-reduction.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Peikert's classical reduction from GapSVP to LWE with exponential modulus](peikert-classical-reduction.md)
- [Leftover hash lemma](../../../randomness-extraction/leftover-hash-lemma.md)

## Sources

- Zvika Brakerski, Adeline Langlois, Chris Peikert, Oded Regev, Damien Stehlé, "Classical Hardness of Learning with Errors", STOC (2013), arXiv:1306.0281.
