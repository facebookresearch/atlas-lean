# Each element is extreme in a uniform random order with probability one over the set size

Let $\alpha$ be a finite set, $\beta$ a finite linearly ordered set with $|\beta| = |\alpha|$, and $S \subseteq \alpha$ nonempty. For a uniformly random bijection $\sigma : \alpha \to \beta$ and every $u \in S$,

$$
\Pr\big[\sigma(u) < \sigma(w) \text{ for all } w \in S \setminus \{u\}\big] = \frac{1}{|S|},
$$

and the same holds with $>$ (each element of $S$ is the maximum with probability $1/|S|$). In particular this holds for uniformly random permutations of a finite linear order.

## Proof sketch

Composing with the transposition of $u$ and $v$ is a bijection between the orders placing $u$ least on $S$ and those placing $v$ least. Since every order has a unique minimum on $S$, these $|S|$ equinumerous classes partition all bijections.

## Sources

- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
