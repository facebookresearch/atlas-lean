# Event characterization, data processing and composition of hockey-stick divergence

Let $p, q$ be discrete probability distributions on a countable set $X$, $c, c_1, c_2 \ge 1$ and $\delta, \delta_2 \ge 0$. For a Markov kernel $K$ from $X$ to a countable set $Y$ write $pK = \sum_x p(x) K(x)$ for the output law.

1. (Events) $E_c(p\|q) = \max_{S \subseteq X}\big(p(S) - c\,q(S)\big)$, attained by the event $\{x : p(x) > c\,q(x)\}$. Hence $p(S) \le c\, q(S) + \delta$ holds for every $S \subseteq X$ if and only if $E_c(p\|q) \le \delta$, and a mechanism $M$ is $(\varepsilon, \delta)$-differentially private if and only if $E_{e^\varepsilon}(M(D)\|M(D')) \le \delta$ for all neighboring $D, D'$.
2. (Data processing) For every Markov kernel $K$, $E_c(pK\|qK) \le E_c(p\|q)$.
3. (Composition) For Markov kernels $K, L$ from $X$ to $Y$ with $E_{c_2}(K(x)\|L(x)) \le \delta_2$ for every $x \in X$, $E_{c_1 c_2}(pK\|qL) \le E_{c_1}(p\|q) + \delta_2$.

## Proof sketch

For item 1, $p(S) - c\,q(S) = \sum_{x \in S}(p(x) - c\,q(x)) \le \sum_x (p(x) - c\,q(x))_+$, with equality on the excess set; the differential-privacy form is the definition of $(\varepsilon, \delta)$-privacy read through this identity. For $c \ge 1$, $E_c$ is the $f$-divergence of $t \mapsto \max(t - c, 0)$, so item 2 is the data processing inequality for $f$-divergences, and item 3 is the sequential composition theorem for this divergence: split the joint excess over $x$ and bound each conditional excess by $\delta_2$ plus the first-stage excess.

The following forms are derived here and are not stated in the cited sources. Item 1 holds for every $c \ge 0$, with the same computation, and more generally $\mathbb{E}_p[g] \le c\,\mathbb{E}_q[g] + E_c(p\|q)$ for every $g : X \to [0, 1]$. Item 2 holds for every $c \ge 0$, since each event of the output pulls back to a $[0,1]$-valued test of the input. For $c_1, c_2 \ge 0$ the triangle inequality $E_{c_1 c_2}(p\|r) \le E_{c_1}(p\|q) + c_1 E_{c_2}(q\|r)$ holds pointwise, from $(a - c_1 c_2 e)_+ \le (a - c_1 b)_+ + c_1 (b - c_2 e)_+$. Item 3 holds for every $c_1, c_2 \ge 0$, for the joint laws of $(x, y)$ in place of the output laws, and with the hypothesis required only on the support of $p$: per $x$, $\sum_y (a K(x)(y) - c_2 b L(x)(y))_+ \le (a - b)_+ + a\,\delta_2$ with $a = p(x)$ and $b = c_1 q(x)$.

## Depends on

- [Hockey-stick divergence](hockey-stick-divergence.md)
- [Differential privacy](../../../ComputerScience/cryptography/differential-privacy/differentially-private.md)

## Sources

- G. Barthe and F. Olmedo, "Beyond Differential Privacy: Composition Theorems and Relational Logic for f-divergences between Probabilistic Programs", International Colloquium on Automata, Languages and Programming (ICALP), 2013, Section 3.1 (the α-distance and Proposition 2) and Section 3.2, Proposition 3 and Theorem 1.
- B. Balle, G. Barthe and M. Gaboardi, "Privacy Amplification by Subsampling: Tight Analyses via Couplings and Divergences", Advances in Neural Information Processing Systems 31 (NeurIPS), 2018, Section 2, equation (2), and Section 3, Theorem 1.
- C. Dwork and A. Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science 9, 2014, Definition 2.4.
- P. Kairouz, S. Oh and P. Viswanath, "The Composition Theorem for Differential Privacy", IEEE Transactions on Information Theory 63(6), 2017.
