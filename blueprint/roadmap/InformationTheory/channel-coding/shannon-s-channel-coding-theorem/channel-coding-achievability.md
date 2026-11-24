# Shannon's channel coding theorem, achievability

Let $W$ be a discrete memoryless channel with finite nonempty input alphabet $\mathcal{A}$ and
finite output alphabet $\mathcal{B}$, and let $C = \max_{P_X} I(X; Y)$ be its capacity in bits, where
$(X, Y)$ has law $P_X(a) W(b \mid a)$. For every rate $R < C$ and every $\varepsilon > 0$, for all
sufficiently large $n$ there is a code of blocklength $n$ with $M \ge 2^{nR}$ codewords
$f(1), \dots, f(M) \in \mathcal{A}^n$ and a decoder $g : \mathcal{B}^n \to \{1, \dots, M\}$ whose
maximal error probability is at most $\varepsilon$:
$W^{\otimes n}(\{y : g(y) \ne m\} \mid f(m)) \le \varepsilon$ for every message $m$.

The proof here follows Gallager (1965), not the cited book. Pick an input law $p$ with
$R < I(p; W)$ (if $R \le 0$ a single code word suffices) and a rate $R'$ in nats with
$R \ln 2 < R' < I(p; W) \ln 2$. Some $0 < \rho \le 1$ has $E = E_0(\rho, p) - \rho R' > 0$. For each
$n$ take $M = \lceil 2^{nR} \rceil$, which is at most $e^{nR'}$ for large $n$. The expurgated random
coding bound gives a code whose every word has error at most
$4 M^\rho e^{-n E_0(\rho, p)} \le 4 e^{-nE}$ under maximum-likelihood decoding, and a
maximum-likelihood decoder errs with at most that probability. For large $n$,
$4 e^{-nE} \le \varepsilon$.

## Informally uses

- [Positive random coding exponent below the mutual information](../random-coding-bound-and-gallager-s-exponent/exists-gallager-e0-sub-pos.md)
- [Expurgated random coding bound, maximal error](../random-coding-bound-and-gallager-s-exponent/exists-code-ml-error-prob-le.md)
- [A maximum-likelihood decoder exists](exists-ml-decoder.md)
- [Maximum-likelihood decoding errs only on ties or worse](measure-real-pi-le-ml-error-prob.md)

## Background

- [Mutual information of a finite joint law](../../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md):
  defines the capacity.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 19.9 with Corollary 19.5 (in particular `C^(max) = C`); C. E. Shannon (1948), Theorem 11.
- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Theorem 1 and Corollary 2 (the route of the proof).
