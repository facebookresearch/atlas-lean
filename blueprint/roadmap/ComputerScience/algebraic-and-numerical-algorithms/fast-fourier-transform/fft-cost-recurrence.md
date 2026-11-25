# The FFT cost satisfies the radix-2 recurrence

Let $C(n) = n \lfloor \log_2 n \rfloor$ be the
closed-form FFT operation count. For every natural number $n > 0$, $C(2n) = 2\,C(n) + 2n$.

Proof: Since $n > 0$, $\lfloor \log_2 (2n) \rfloor = \lfloor \log_2 n \rfloor + 1$; expand the
product.

## Sources

- J. W. Cooley and J. W. Tukey, Math. Comp. 19 (1965) (`n log n` operation count).
