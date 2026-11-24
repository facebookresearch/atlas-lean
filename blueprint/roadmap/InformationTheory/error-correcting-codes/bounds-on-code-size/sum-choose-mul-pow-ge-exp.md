# Volume of a Hamming ball, entropy lower bound

Let $q \ge 2$ and $0 \le p \le 1$. For every $\eta > 0$ and all large enough $n$,

$$\mathrm{Vol}_q(n, \lfloor pn \rfloor) = \sum_{i=0}^{\lfloor pn \rfloor} \binom{n}{i} (q-1)^i \ge \exp\bigl(n \, H(q, p) - \eta n\bigr),$$

where $H(q, p) = p \log (q-1) - p \log p - (1-p) \log (1-p)$ (natural logarithm, $0 \log 0 = 0$). In base $q$ this is
$\mathrm{Vol}_q(n, pn) \ge q^{H_q(p) n - o(n)}$, Proposition 3.3.3 (ii) of Guruswami, Rudra and
Sudan, stated there for $0 \le p \le 1 - 1/q$; the $o(n)$ term is written $\eta n$ for an
arbitrary $\eta > 0$. With the [upper bound](sum-choose-mul-pow-le-exp.md) it shows
$\mathrm{Vol}_q(n, pn) = q^{H_q(p) n + o(n)}$ for $p \le 1 - 1/q$.

The proof keeps the single term $i = m = \lfloor pn \rfloor$, which is at least
$\exp(n H(q, m/n)) / (n + 1)$ ([largest term](choose-mul-pow-ge.md)); then
$|m/n - p| < 1/n$, the entropy is uniformly continuous on $[0, 1]$, and
$\log(n + 1) = o(n)$. Guruswami, Rudra and Sudan use Stirling's approximation instead.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Proposition 3.3.3 (ii).
