# A shifted central binomial series with odd harmonic numbers

For every natural number $h$,
write $H_h = \sum_{j=1}^{h} \frac{1}{j}$, $H^{(2)}_h = \sum_{j=1}^{h} \frac{1}{j^2}$ and
$O_n = \sum_{j=1}^{n} \frac{1}{2j - 1}$. Then

$$\sum_{n=0}^{\infty} \frac{\binom{2n}{n} O_n}{\binom{n+h}{h} \binom{2(n+h+1)}{n+h+1} (n + h + 1)^2}
= -\frac{(-1)^h \bigl(\frac{\pi^2}{6} - H^{(2)}_h\bigr)}{2 (h + 1) \binom{2(h+1)}{h+1}} +
\frac{(-1)^h (H_h + 2 \log 2) \, O_{h+1}}{(h + 1) \binom{2(h+1)}{h+1}} -
\sum_{n=0}^{h-1} \frac{(-1)^{h-n} \binom{h}{n} \, O_{h-n}}
{\binom{2(h-n)}{h-n} \binom{2(n+1)}{n+1} (n+1)^2}.$$

After replacing $n$ by $n - h$, the left side is
$\sum_{n \ge h} \binom{2(n-h)}{n-h} O_{n-h} /
\bigl(\binom{n}{h} \binom{2(n+1)}{n+1} (n + 1)^2\bigr)$.

## Sources

- Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 9, identity (22).
