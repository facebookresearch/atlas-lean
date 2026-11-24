# First-order estimate along a segment, one letter

For $p, p^* \ge 0$, $q > 0$ and $0 < t < 1$, with $p_t = p^* + t(p - p^*)$:

$$p_t\log\frac{p_t}{q} - p^*\log\frac{p^*}{q} \le t\bigl((p - p^*)(\log p_t - \log q) + (p - p^*)\bigr).$$

Summed over the alphabet, the last term vanishes for distributions and the left side is
$D(P_t\|Q) - D(P^*\|Q)$; this is the estimate behind the
[first-order condition](first-order-condition-for-i-projections.md).

## Sources

- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, proof of Theorem 3.1.
