# Duration of a logistic sweep between two frequencies

For real numbers $s, a, b$, the sweep duration from frequency $a$ to frequency $b$ is

$$\tau_s(a, b) = \frac{1}{s} \log \frac{b (1 - a)}{a (1 - b)},$$

with the conventions $x/0 = 0$, $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. For $0 < a, b < 1$ and $s \ne 0$ it is the difference of the logits of $b$ and $a$ divided by $s$: the time a logistic sweep with selection coefficient $s$ takes from frequency $a$ to frequency $b$ (positive when $s > 0$ and $a < b$).
