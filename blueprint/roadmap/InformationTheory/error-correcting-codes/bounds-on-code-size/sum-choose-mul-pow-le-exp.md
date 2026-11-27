# Volume of a Hamming ball, entropy upper bound

Let $q \ge 2$, $0 \le p \le 1 - 1/q$, and let $e \le pn$ be a natural number. Then

$$\mathrm{Vol}_q(n, e) = \sum_{i=0}^{e} \binom{n}{i} (q-1)^i \le \exp\bigl(n \, H(q, p)\bigr) = q^{H_q(p) n},$$

where $H(q, p) = p \log (q-1) - p \log p - (1-p) \log (1-p)$ (natural
logarithm, $0 \log 0 = 0$) and $H_q(p) = H(q, p) / \log q$ is the $q$-ary entropy of Definition 3.3.1 in
Guruswami, Rudra and Sudan.

The proof compares each term with the binomial expansion of $(p + (1-p))^n = 1$: for $i \le pn$,
$(q-1)^i q^{-H_q(p) n} \le p^i (1-p)^{n-i}$ because $p / ((q-1)(1-p)) \le 1$.

The matching [lower bound](sum-choose-mul-pow-ge-exp.md)
$\mathrm{Vol}_q(n, \lfloor pn \rfloor) \ge q^{H_q(p) n - o(n)}$ (Proposition 3.3.3 (ii)) holds as
well.

## Background

- [Size of a Hamming ball](card-ball.md): the exact volume formula.
- [Bounds on partial sums of binomial coefficients](../../../Combinatorics/binomial-coefficients/binomial-sums/bounds-on-partial-sums-of-binomial-coefficients/README.md): sibling estimates of the same partial sums $\sum_{i \le r} \binom{D}{i}$, of the form $(e D / r)^r$ rather than entropy bounds.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definitions 3.3.1 and 3.3.2 and Proposition 3.3.3 (i).
