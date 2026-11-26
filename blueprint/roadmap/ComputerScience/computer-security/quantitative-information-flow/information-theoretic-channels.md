# Information-theoretic channels

A *channel* is a triple $(\mathcal X, \mathcal Y, C)$ where $\mathcal X$ is a finite **nonempty** set of secret inputs, $\mathcal Y$ a finite set of observable outputs, and $C$ is a channel matrix: an
$|\mathcal X| \times |\mathcal Y|$ matrix with entries in $[0, 1]$ whose rows each sum to $1$, $C[x, y]$ being the probability of output $y$ on input $x$; row normalization forces $\mathcal Y \ne \emptyset$. $C$ is
*deterministic* if every entry is $0$ or $1$, so that each input $x$ produces a unique output $C(x)$.

A *prior* is a probability distribution $\pi$ on $\mathcal X$; the *uniform prior* is $\pi_u[x] = 1/|\mathcal X|$. Together, $\pi$ and $C$ give the joint distribution $p(x, y) = \pi[x]\, C[x, y]$ on $\mathcal X \times \mathcal Y$,
the unique one with marginal $p(x) = \pi[x]$ and conditional $p(y \mid x) = C[x, y]$ when $\pi[x] > 0$. The *cascade* of channels $C_1$ from $\mathcal X$ to $\mathcal Y$ and
$C_2$ from $\mathcal Y$ to $\mathcal Z$ is the channel $C_1 C_2$ from $\mathcal X$ to $\mathcal Z$ given by the matrix product.

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section II (channels, priors and the joint distribution) and Theorem 6.1 (cascades as products of channel matrices).
