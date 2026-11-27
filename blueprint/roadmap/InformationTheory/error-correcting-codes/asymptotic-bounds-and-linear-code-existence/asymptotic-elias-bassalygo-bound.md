# The asymptotic Elias-Bassalygo bound

Let $q \ge 2$, $H_q$ the $q$-ary entropy (in nats, divided by $\ln q$ to give $q$-ary units) and $J_q(\delta) = (1 - 1/q)\bigl(1 - \sqrt{1 - q\delta/(q - 1)}\bigr)$ the $q$-ary Johnson radius. For a code $C$ of length $n \ge 1$ with minimum distance at least $d$, where $d \le (1 - 1/q)\, n$, and an integer $e$ with $e/n < J_q(d/n)$,

$$\mathrm{rate}(C) = \frac{\log_q |C|}{n} \le 1 - H_q\!\left(\frac en\right) + \frac{\log_q\bigl((q - 1)\, n\, d\, (n + 1)\bigr)}{n}.$$

Hence for any family of codes with lengths tending to infinity and relative distance at least $\delta$, $0 \le \delta \le 1 - 1/q$, and every $\varepsilon > 0$, eventually $\mathrm{rate}(C_s) \le 1 - H_q(J_q(\delta)) + \varepsilon$.

## Proof sketch

Averaging over balls of radius $e$ shows some ball contains at least $|C|\,\mathrm{Vol}_q(n, e)/q^n$ codewords, while the $q$-ary Johnson bound caps any such ball by $(q - 1) n d$. The entropy lower bound on the ball volume converts this into the rate bound, and letting $e/n \to J_q(\delta)$ with continuity of $H_q$ gives the asymptotic form.

## Depends on

- [q-ary Johnson radius](../list-decoding/johnson-radius.md)
- [Minimum distance](../linear-codes/min-dist.md)

## Proof depends on

- [Elias–Bassalygo bound (alphabet-free form)](../bounds-on-code-size/elias-bassalygo-bound.md)
- [Johnson bound](../list-decoding/johnson-bound.md)

## Sources

- L. A. Bassalygo, "New Upper Bounds for Error-Correcting Codes", Problems of Information Transmission, 1965.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
