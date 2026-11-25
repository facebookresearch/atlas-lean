# The Laplace mechanism is differentially private

Let $f : X \to \mathbb{R}$ satisfy $|f(x) - f(y)| \le \Delta$ for all neighbours $x, y$, with
$\Delta > 0$, and let $\varepsilon > 0$. The Laplace mechanism with scale $\Delta / \varepsilon$ is
$\varepsilon$-differentially private: the densities of the outputs on neighbouring databases differ by
a factor of at most $e^{|f(x) - f(y)| \varepsilon / \Delta} \le e^{\varepsilon}$. Any upper bound
$\Delta$ on the sensitivity works; the source uses the sensitivity itself.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 3.6 for $k = 1$.
- C. Dwork, F. McSherry, K. Nissim and A. Smith, *Calibrating noise to sensitivity in private data analysis*, TCC 2006 (the Laplace mechanism, cited in Dwork and Roth 2014, Section 3.7).
