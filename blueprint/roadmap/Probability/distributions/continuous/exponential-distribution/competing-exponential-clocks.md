# Competing exponential clocks

Let $k \ge 1$ and let $T_1, \dots, T_k$ be independent exponential random variables with rates $q_1, \dots, q_k > 0$, let $q = q_1 + \dots + q_k$, $T = \min_j T_j$, and $J$ the index attaining the minimum, which is almost surely unique. Then $\mathbb{P}(T > t, J = j) = (q_j/q)e^{-qt}$ for all $t \ge 0$ and all $j$: $T$ is exponential with rate $q$, $\mathbb{P}(J = j) = q_j/q$, and $T$ and $J$ are independent. For two clocks with rates $a, b > 0$ this gives $\mathbb{P}(T_1 < T_2) = a/(a + b)$, also in the product-measure form $(\mathrm{Exp}(a) \otimes \mathrm{Exp}(b))(\{(x, y) : x < y\}) = a/(a + b)$ and for independent, merely a.e.-measurable random variables with these laws, whose joint law is that product. This is the one-step link between an event model with independent exponential clocks and the holding time and jump law of a continuous-time Markov chain.

Proof. By independence, $\mathbb{P}(T > t, J = j) = \int_t^\infty q_j e^{-q_j s}\prod_{l \ne j} e^{-q_l s}\,ds = (q_j/q)e^{-qt}$; ties have probability zero because the $T_j$ are independent with densities. Summing over $j$ gives $\mathbb{P}(T > t) = e^{-qt}$, and $t = 0$ gives $\mathbb{P}(J = j) = q_j/q$.

## Background

- [Finite-dimensional distributions](../../../markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md): finite-dimensional laws of the continuous-time Markov chain path.

## Sources

- K. Sigman, *Continuous-Time Markov Chains* (lecture notes, IEOR 6711), Columbia University, 2009, Section 1.5 (Birth and Death processes), holding time and jump probabilities, <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-CTMC.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
