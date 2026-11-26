# The rewinding lemma

Let $S$ be a set, $T$ a finite non-empty set and $f : S \times T \to \{0, 1\}$ a function. Let $X$, $Y$ and $Y'$ be mutually independent random variables, where $X$ is a discrete random variable with values in $S$ and $Y$ and $Y'$ are each uniformly distributed over $T$. Let $\varepsilon = \Pr[f(X, Y) = 1]$ and $N = |T|$. Then

$$\Pr\bigl[f(X, Y) = 1 \wedge f(X, Y') = 1 \wedge Y \ne Y'\bigr] \ge \varepsilon^2 - \varepsilon/N.$$

## Remarks

Boneh and Shoup state the lemma for a finite set $S$; the bound holds for every discrete distribution of $X$.

In a security reduction $X$ collects the random choices of an adversary other than a challenge $Y$; running the adversary once with challenge $Y$ and again on the same $X$ with a fresh challenge $Y'$ yields, with this probability, two successful runs on distinct challenges.

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Lemma 19.2
