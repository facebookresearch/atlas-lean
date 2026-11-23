# Chernoff bound for a sub-exponential variable

Let $\mu$ be a probability measure and $X$ sub-exponential with parameters $(\nu, \alpha)$. For
every real $t$ and every $s \ge 0$ with $\alpha s \le 1$,

$$\mu(X \ge t) \le \exp\Big(-s t + \frac{\nu^2 s^2}{2}\Big).$$

The endpoint $s = 1/\alpha$, where the moment generating function bound is not assumed, follows by
letting $s$ increase to $1/\alpha$.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.1.3, proof of the sub-exponential tail bound.
- A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3, Carnegie Mellon University, 2017: <https://www.stat.cmu.edu/~arinaldo/Teaching/36755/F17/Scribed_Lectures/F17_0911.pdf>, proof of Theorem 3.2.
