# Correctness of the saturating round-half-up quantizer

Let $\Delta > 0$ and let $k_{\min} \le k_{\max}$ be integers. Let $Q(x) = \Delta \cdot \max\bigl(k_{\min}, \min(k_{\max}, \lfloor x/\Delta + 1/2 \rfloor)\bigr)$ and let $\pi(x)$ be the nearest point of $[\Delta k_{\min}, \Delta k_{\max}]$ to $x$. Then:

1. $Q$ is monotone;
2. for every $x \in [\Delta k_{\min}, \Delta k_{\max}]$, $|Q(x) - x| \le \Delta/2$;
3. for every $x \in \mathbb{R}$, $|Q(x) - x| \le |x - \pi(x)| + \Delta/2$.
