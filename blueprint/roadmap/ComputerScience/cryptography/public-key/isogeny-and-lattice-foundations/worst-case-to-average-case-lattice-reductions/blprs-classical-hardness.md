# Classical hardness of LWE with polynomial modulus

There are a polynomial modulus $q=q(n)$, a Gaussian error rate $\alpha=\alpha(n)$ with $1/\alpha$ polynomial in $n$, an approximation factor $\gamma=\mathrm{poly}(n)$ and a classical polynomial-time reduction from worst-case $\mathrm{GapSVP}_\gamma$ in dimension $\sqrt{n}$ to decision LWE in dimension $n$ with modulus $q$ and error rate $\alpha$. The key ingredients are a modulus-switching reduction from LWE with modulus $q$ in dimension $n$ to LWE with modulus $q'$ in dimension $n\log q/\log q'$ (with a small increase in error), and the classical reduction for exponential moduli.

## Proof sketch

Apply Peikert's classical reduction with exponential modulus in dimension $\sqrt{n}$. Then trade modulus for dimension: LWE with secret in dimension $k$ and modulus $q^{k'}$ reduces to LWE in dimension $kk'$ with modulus $q$, via a gadget decomposition of secrets combined with LWE with binary secrets (shown hard by an entropic leftover-hash argument). Error growth is controlled by modulus switching with rounding.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)

## Proof depends on

- [Peikert's classical reduction from GapSVP to LWE with exponential modulus](peikert-classical-reduction.md)
- [Leftover hash lemma](../../../randomness-extraction/leftover-hash-lemma.md)

## Sources

- Zvika Brakerski, Adeline Langlois, Chris Peikert, Oded Regev, Damien Stehlé, "Classical Hardness of Learning with Errors", STOC (2013), arXiv:1306.0281.
