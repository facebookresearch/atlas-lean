# Wakefield's Bayes factor is a Radon–Nikodym derivative

Let $P$ be a probability measure on a measurable space $\Omega$, and let $\beta$ and $\varepsilon$ be measurable real random variables that are independent under $P$. Let $V$ and $W$ be nonnegative reals with $V \ne 0$, and suppose that $\beta$ has law $N(0, W)$ and $\varepsilon$ has law $N(0, V)$ under $P$. Then the Radon–Nikodym derivative of the law of $\beta + \varepsilon$ with respect to the law of $\varepsilon$ equals $b \mapsto \mathrm{ABF}(V, W, b)$ almost everywhere with respect to the law of $\varepsilon$, where $\mathrm{ABF}$ is [Wakefield's approximate Bayes factor](wakefield-abf.md).

In words: for an estimate $\beta + \varepsilon$ of an effect $\beta$ with sampling error $\varepsilon$, the approximate Bayes factor is the Bayes factor of the alternative $\beta \sim N(0, W)$ against the null $\beta = 0$.
