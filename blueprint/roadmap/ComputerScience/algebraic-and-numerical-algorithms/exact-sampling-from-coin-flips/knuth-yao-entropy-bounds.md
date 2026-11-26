# Knuth-Yao theorem: optimal sampling from fair bits costs between H(p) and H(p)+2 flips

Let $p$ be a probability distribution on a finite set $\alpha$ and let $H(p) = -\sum_a p(a)\log_2 p(a)$ be its Shannon entropy in bits. Let $\tau_T$ be the number of fair bits read by a DDG tree $T$.

1. (Stochastic optimality) The Knuth-Yao tree $T_{KY}$ of $p$ generates $p$, and for every tree $T$ generating $p$ and every $n \ge 0$, $\Pr[\tau_{T_{KY}} > n] \le \Pr[\tau_T > n]$; in particular $T_{KY}$ minimizes $\mathbb{E}[\tau_T]$ among all trees generating $p$.
2. (Entropy bounds) Every tree generating $p$ satisfies $\mathbb{E}[\tau_T] \ge H(p)$, and $\mathbb{E}[\tau_{T_{KY}}] < H(p) + 2$.
3. (Dyadic case) Some tree generating $p$ has $\mathbb{E}[\tau_T] = H(p)$ if and only if every positive mass $p(a)$ is an integer power of $1/2$.

## Proof sketch

After $n$ fair bits any tree has produced $a$ with a dyadic probability $c/2^n \le p(a)$, hence $c \le \lfloor 2^n p(a)\rfloor$, which is the Knuth-Yao count; this gives the tail comparison. The expected cost of the Knuth-Yao tree is $\sum_a \nu(p(a))$, and the elementary bounds $x\log_2(1/x) \le \nu(x) < x\log_2(1/x) + 2x$ for $0 < x \le 1$ give both entropy bounds after summing. Equality $\nu(x) = x\log_2(1/x)$ holds exactly at $x = 0$ and at powers of $1/2$.

## Depends on

- [Knuth-Yao sampling tree of a finite distribution](knuth-yao-tree.md)
- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Proof depends on

- [Knuth-Yao sampling tree of a finite distribution](knuth-yao-tree.md)
- [Discrete distribution generating (DDG) tree](ddg-tree.md)

## Sources

- Donald E. Knuth and Andrew C. Yao, "The Complexity of Nonuniform Random Number Generation", in Algorithms and Complexity: New Directions and Recent Results, Academic Press, 1976.
- Thomas M. Cover and Joy A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
