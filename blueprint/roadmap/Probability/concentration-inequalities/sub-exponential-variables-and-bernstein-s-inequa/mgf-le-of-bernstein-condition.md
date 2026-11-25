# Bernstein's moment generating function bound

Let $\mu$ be a probability measure and $X$ a centred random variable with all moments finite and
$\mathbb{E}[X^2] = \sigma^2$, satisfying the *Bernstein condition* with parameter $b \ge 0$:

$$\big|\mathbb{E}[X^k]\big| \le \tfrac12\, k!\, \sigma^2 b^{k-2} \quad \text{for } k = 3, 4, \dots$$

Then for every $t$ with $b|t| < 1$ the function $e^{tX}$ is integrable and
$\mathbb{E}[e^{tX}] \le \exp\big(t^2\sigma^2 / (2(1 - b|t|))\big)$.

The proof expands the exponential in series and integrates termwise.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.1.3 (Bernstein bounds).
- A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3, Carnegie Mellon University, 2017: <https://www.stat.cmu.edu/~arinaldo/Teaching/36755/F17/Scribed_Lectures/F17_0911.pdf>, Definition 3.3 and Theorem 3.4.

## Background

- [Bernstein's bound on the moment generating function of a bounded variable](mgf-le-of-abs-le.md): the special case $|X| \le b$.
