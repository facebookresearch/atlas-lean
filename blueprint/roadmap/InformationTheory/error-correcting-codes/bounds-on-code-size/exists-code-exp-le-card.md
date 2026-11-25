# Gilbert–Varshamov bound, rate form

Let $\alpha$ be an alphabet with $q \ge 2$ letters, let $0 \le \delta \le 1 - 1/q$, and let $n$
and $d$ be natural numbers with $1 \le d$ and $d - 1 \le \delta n$. There is a code
$C \subseteq \alpha^n$ in which any two distinct codewords are at Hamming distance at least $d$
and

$$|C| \ge \exp\bigl(n (\log q - H(q, \delta))\bigr) = q^{(1 - H_q(\delta)) n},$$

where $H(q, \delta) = \delta \log (q-1) - \delta \log \delta - (1-\delta) \log (1-\delta)$ (natural
logarithm, $0 \log 0 = 0$) and $H_q(\delta) = H(q, \delta) / \log q$ is the
$q$-ary entropy. When $\delta n > 0$, taking $d = \lceil \delta n \rceil$ gives a code of rate at
least $1 - H_q(\delta)$ and relative distance at least $\delta$: this is the general-code part of
Theorem 4.2.1 of Guruswami, Rudra and Sudan, there stated for $0 \le \delta < 1 - 1/q$.

## Informally uses

- [Gilbert–Varshamov bound](exists-code-pow-le-card-mul-sum.md): $q^n \le |C| \cdot \mathrm{Vol}_q(n, d-1)$.
- [Volume of a Hamming ball, entropy upper bound](sum-choose-mul-pow-le-exp.md):
  $\mathrm{Vol}_q(n, d-1) \le q^{H_q(\delta) n}$ since $d - 1 \le \delta n$.

## Background

- [CSS codes](../../../QuantumInformation/quantum-error-correction/css-codes/README.md): the
  asymptotic rate $1 - 2H_2(2t/n)$ of Calderbank and Shor's good quantum codes, recorded there, is
  a bound of Gilbert–Varshamov type for pairs of classical codes.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 4.2.1 and Proposition 3.3.3 (i).
