# Shannon source coding lower bound

Let $\alpha$ and $\beta$ be finite types with
$q = |\beta| \ge 2$, and let $p : \alpha \to \mathbb{R}$ satisfy $p(a) > 0$ for every $a \in \alpha$
and $\sum_{a \in \alpha} p(a) = 1$. Let $c$ assign to each $a \in \alpha$ a finite word $c(a)$ over
$\beta$, of length $|c(a)|$, such that $c$ is injective and its set of codewords is uniquely
decodable: any two finite lists of codewords with the same concatenation are equal. Then the
expected length $\sum_{a \in \alpha} p(a)\,|c(a)|$ is at least the base-$q$ entropy
$-\left(\sum_{a \in \alpha} p(a) \log p(a)\right) / \log q$, where $\log$ is the natural logarithm.

## Sources

- C. E. Shannon, Bell Syst. Tech. J. 27 (1948), 379-423 and 623-656, DOI 10.1002/j.1538-7305.1948.tb01338.x.
