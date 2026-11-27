# Classical hardness of LWE with polynomial modulus

There are a polynomial modulus $q=q(n)$, a Gaussian error rate $\alpha=\alpha(n)$ with $1/\alpha$ polynomial in $n$, an approximation factor $\gamma=\mathrm{poly}(n)$ and a classical polynomial-time reduction from worst-case $\mathrm{GapSVP}_\gamma$ in dimension $\sqrt{n}$ to decision LWE in dimension $n$ with modulus $q$ and error rate $\alpha$. The key ingredients are a reduction from LWE in dimension $k$ with a large modulus $Q$ to LWE with secrets in $\{0,1\}$ in dimension $n'\ge(k+1)\log_2 Q+2\log_2(1/\delta)$, where $\delta$ bounds the loss in advantage (Theorem 4.1), followed by modulus switching, which for such short secrets reduces the modulus to a polynomial one with a small increase in error (Corollary 3.2). Together they reduce dimension-$k$ LWE with modulus $Q$ to LWE in dimension about $k\log_2 Q$ with polynomial modulus; the result follows by applying them to Peikert's classical reduction for exponential moduli in dimension $k=\sqrt{n}$ with $Q=2^{k/2}$. (Their Corollary 3.4 trades the other way, from dimension $n$ and modulus $q$ to dimension $n/k$ and modulus $q^{k}$.)

## Proof sketch

Apply Peikert's classical reduction in dimension $k=\sqrt{n}$ with modulus $Q=2^{k/2}$, together with a search-to-decision reduction for power-of-two moduli. Then reduce this decision LWE problem to LWE with a binary secret in dimension about $k\log_2 Q$: first to a variant whose first equation is errorless, then to an extended LWE problem that leaks some information about the noise, and finally to binary-secret LWE, using an entropy (leftover-hash-type) argument over the binary secret. Because binary secrets are short, rounding the samples to a polynomial modulus with Gaussian rounding increases the error only slightly.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)

## Proof depends on

- [Peikert's classical reduction from GapSVP to LWE with exponential modulus](peikert-classical-reduction.md)
- [Leftover hash lemma](../../../randomness-extraction/leftover-hash-lemma.md)

## Sources

- Zvika Brakerski, Adeline Langlois, Chris Peikert, Oded Regev, Damien Stehlé, "Classical Hardness of Learning with Errors", STOC (2013), arXiv:1306.0281, Section 1, Corollaries 3.2 and 3.4, and Theorem 4.1.
