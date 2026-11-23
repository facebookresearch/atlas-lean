# A Borel set of L^p functions with vanishing integrals

Let $1 \le p \le \infty$. The set of real-valued $f \in L^p(\mathbb{R})$, for Lebesgue measure,
such that $\int_0^L f(x)\, dx \to 0$ as $L \to +\infty$ is a Borel subset of $L^p(\mathbb{R})$.

## Idea

For each fixed $L$, the map $f \mapsto \int_0^L f$ is continuous on $L^p(\mathbb{R})$, by Hölder's
inequality on the bounded interval $[0, L]$, and it depends continuously on $L$. So the condition
"the integrals tend to $0$" can be written with countably many quantifiers over rational $L$: for
every $k$ there is $N$ such that $|\int_0^L f| \le 1/k$ for every rational $L \ge N$. This presents
the set as a countable intersection of countable unions of closed sets.

## Statements

- [$L^p$ functions whose integrals over $(0, L)$ tend to $0$ form a Borel set](measurable-set-vanishing-integral-set.md)
- [Functions with vanishing integrals over $(0, L)$](vanishing-integral-set.md): the set of the statement.
