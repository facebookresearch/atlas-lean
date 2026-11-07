# Generating function of the Leonardo numbers

Let $Le_n$ be the Leonardo numbers
($Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$), and let
$L(t) = \sum_{n \ge 0} Le_n t^n$ in the ring $\mathbb{Z}[[t]]$ of formal power series. Then
$L(t)(1 - 2t + t^3) = 1 - t + t^2$ and $L(t)(1 - t - t^2)(1 - t) = 2(1 - t) - (1 - t - t^2)$.

Equivalently, $L(t) = \frac{2}{1-t-t^2} - \frac{1}{1-t} = \frac{1-t+t^2}{1-2t+t^3}$; the
identities above are this equality with the denominators cleared.

## Sources

- Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 2 (`integers-2026-A48-cor-2`).
