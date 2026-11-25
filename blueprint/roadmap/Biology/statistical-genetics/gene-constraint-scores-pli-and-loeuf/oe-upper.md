# Upper confidence bound for the observed/expected ratio

For real numbers $\alpha$ and $E$ and a natural number $o$, the upper bound for the observed/expected ratio at level $\alpha$ is

$$U_\alpha(E, o) = \frac{u_\alpha(o)}{E}, \qquad u_\alpha(o) = \sup\Bigl\{x \ge 0 : \alpha \le \sum_{j=0}^{o} \frac{e^{-x} x^j}{j!}\Bigr\},$$

where $u_\alpha(o)$ is Garwood's upper bound for a Poisson mean after observing $o$, with the conventions that the supremum of an empty or unbounded set is $0$ and $x/0 = 0$. For $0 < \alpha < 1$, $u_\alpha(o)$ is the root $u$ of $\sum_{j=0}^{o} e^{-u} u^j / j! = \alpha$, and for $E > 0$, $U_\alpha(E, o)$ is a one-sided upper confidence bound of level $1 - \alpha$ for the ratio of the Poisson mean of the observed count to $E$.
