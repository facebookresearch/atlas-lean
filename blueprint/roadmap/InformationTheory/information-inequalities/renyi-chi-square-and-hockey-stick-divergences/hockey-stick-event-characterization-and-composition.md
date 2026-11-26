# Event characterization, data processing and composition of hockey-stick divergence

Let $p, q, r$ be discrete probability distributions on a countable set $X$ and $c, c_1, c_2 \ge 0$, $\delta \ge 0$.

1. (Events) $p(S) \le c\, q(S) + \delta$ holds for every $S \subseteq X$ if and only if $E_c(p\|q) \le \delta$; the event $\{x : p(x) > c\,q(x)\}$ attains the excess. More generally $\mathbb{E}_p[g] \le c\,\mathbb{E}_q[g] + E_c(p\|q)$ for every $g : X \to [0,1]$. Thus a mechanism $M$ is $(\varepsilon, \delta)$-differentially private iff $E_{e^\varepsilon}(M(D)\|M(D')) \le \delta$ for all neighboring $D, D'$.
2. (Data processing) For every Markov kernel $K$, $E_c(pK\|qK) \le E_c(p\|q)$.
3. (Triangle) $E_{c_1 c_2}(p\|r) \le E_{c_1}(p\|q) + c_1 E_{c_2}(q\|r)$.
4. (Adaptive composition) If $E_{c_2}(K(x)\|L(x)) \le \delta_2$ for every $x$ in the support of $p$, then the joint laws of $(x, y)$ satisfy $E_{c_1 c_2} \le E_{c_1}(p\|q) + \delta_2$.

## Proof sketch

For item 1, $p(S) - c\,q(S) = \sum_{x \in S}(p(x) - c\,q(x)) \le \sum_x (p(x) - c\,q(x))_+$ with equality on the excess set, and the same computation works for $[0,1]$-valued $g$. Data processing follows from item 1 since each event of the output pulls back to a $[0,1]$-valued test of the input. The triangle inequality is pointwise: $(a - c_1c_2 e)_+ \le (a - c_1 b)_+ + c_1(b - c_2 e)_+$. For composition, split the joint excess over $x$ and bound each conditional excess by $\delta_2$ plus the first-stage excess.

## Depends on

- [Hockey-stick divergence](hockey-stick-divergence.md)
- [Differential privacy](../../../ComputerScience/cryptography/differential-privacy/differentially-private.md)

## Sources

- C. Dwork and A. Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science 9, 2014.
- P. Kairouz, S. Oh and P. Viswanath, "The Composition Theorem for Differential Privacy", IEEE Transactions on Information Theory 63(6), 2017.
