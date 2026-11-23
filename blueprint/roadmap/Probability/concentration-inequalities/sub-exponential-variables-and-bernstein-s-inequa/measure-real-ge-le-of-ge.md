# Sub-exponential tail bound, exponential regime

Let $\mu$ be a probability measure and $X$ sub-exponential with parameters $(\nu, \alpha)$ with
$\alpha > 0$. For every $t \ge \nu^2/\alpha$,

$$\mu(X \ge t) \le \exp\Big(-\frac{t}{2\alpha}\Big).$$

Together with the Gaussian regime this gives
$\mu(X \ge t) \le \exp(-\tfrac12 \min(t^2/\nu^2,\, t/\alpha))$ for all $t \ge 0$.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.1.3 (sub-exponential tail bound).
- A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3, Carnegie Mellon University, 2017: <https://www.stat.cmu.edu/~arinaldo/Teaching/36755/F17/Scribed_Lectures/F17_0911.pdf>, Theorem 3.2.
