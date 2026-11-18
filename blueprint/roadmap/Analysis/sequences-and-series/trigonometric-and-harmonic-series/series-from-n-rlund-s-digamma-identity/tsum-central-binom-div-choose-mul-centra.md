# A shifted central binomial series

For every natural number $h$, with
$H_h = \sum_{j=1}^{h} \frac{1}{j}$ the $h$th harmonic number,

$$\sum_{n=0}^{\infty} \frac{\binom{2n}{n}}{\binom{n+h}{h} \binom{2(n+h+1)}{n+h+1} (n + h + 1)^2} =
\frac{(-1)^h (H_h + 2 \log 2)}{(h + 1) \binom{2(h+1)}{h+1}} -
\sum_{n=0}^{h-1} \frac{(-1)^{h-n} \binom{h}{n}}{\binom{2(h-n)}{h-n} \binom{2(n+1)}{n+1} (n+1)^2}.$$

After replacing $n$ by $n - h$, the left side is
$\sum_{n \ge h} \binom{2(n-h)}{n-h} / \bigl(\binom{n}{h} \binom{2(n+1)}{n+1} (n + 1)^2\bigr)$.

## Sources

- Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of Nörlund*, INTEGERS 25 (2025), Article A18, Corollary 2, identity (20).
