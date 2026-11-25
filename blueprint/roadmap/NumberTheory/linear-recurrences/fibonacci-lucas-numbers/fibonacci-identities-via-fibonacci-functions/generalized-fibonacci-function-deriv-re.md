# Real part of the derivative of the generalized Fibonacci function at integers

Let $p$
be a real number and let $W : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = p W_{j+1} + W_j$ for
every integer $j$. Put $\delta = \sqrt{p^2 + 4}$, $\sigma = (p + \delta)/2$,
$\tau = (p - \delta)/2$, $A = W_1 - W_0 \tau$ and $B = W_1 - W_0 \sigma$. For an integer $m$,
define $w : \mathbb{R} \to \mathbb{C}$ by

$$
w(x) = \frac{A \sigma^x - B (-\tau)^x e^{i \pi (2m + 1) x}}{\delta}.
$$

Then for every integer $j$, $\operatorname{Re} w'(j) = (W_{j+1} + W_{j-1}) \ln \sigma / \delta$.

Since $\tau < 0$, $w(x)$ is $(A \sigma^x - B \tau^x)/\delta$ with $\tau^x$ read on the branch
$(-\tau)^x e^{i \pi (2m + 1) x}$; this is the generalized Fibonacci function of the journal text.

## Sources

- Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27 (2024), Article 24.6.2, Theorem 15 (`jis-2024-24.6.2-thm-15`).
