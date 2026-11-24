# Detailed balance for a Gibbs update

Let $\pi$ be a probability distribution on the
configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every
$x$, and for a coordinate $i$ let $P_i(x, y)$ be the probability that the Gibbs update of
coordinate $i$ moves $x$ to $y$. Then $\pi(x) P_i(x, y) = \pi(y) P_i(y, x)$ for all
configurations $x$ and $y$.

When $x$ and $y$ differ at most in coordinate $i$, both sides equal $\pi(x) \pi(y) / Z$ for the
same normalizer $Z$; otherwise both sides are $0$.
