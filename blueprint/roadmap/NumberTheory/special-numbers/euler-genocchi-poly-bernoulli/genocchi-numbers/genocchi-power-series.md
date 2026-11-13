# Generating function of the Genocchi numbers

The Genocchi power series is the formal power
series $\frac{2x}{e^x + 1} = 2x \cdot (e^x + 1)^{-1}$ in $\mathbb{Q}[[x]]$, where
$e^x = \sum_{n \ge 0} x^n / n!$ is the exponential power series and $(e^x + 1)^{-1}$ is the inverse
of $e^x + 1$ among formal power series. It is the exponential generating function of the Genocchi
numbers $G_n$, that is, $\frac{2x}{e^x + 1} = \sum_{n \ge 0} G_n \frac{x^n}{n!}$.

This retains the standard convention $\frac{2x}{e^x + 1}$ stated by Chen and used independently by
Kida; the sign-changed variant consumes only even-index terms, where the conventions agree.

## Sources

- Chen, JIS VOL6 (`chen50.tex`, lines 296-300): https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.html
- Kida, JIS VOL16: https://cs.uwaterloo.ca/journals/JIS/VOL16/Kida/kida2.html
