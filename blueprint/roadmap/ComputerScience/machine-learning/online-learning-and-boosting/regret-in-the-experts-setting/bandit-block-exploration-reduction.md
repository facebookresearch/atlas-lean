# Block-exploration reduction from bandit feedback to full information: regret $O(T^{2/3} N^{1/3} \ln N)$

In the partial-information (multi-armed bandit) experts model, an oblivious adversary fixes losses $\ell_t \in [0,1]^X$ for $N = |X| \ge 1$ arms, and the learner observes only the loss of the arm it plays.

Let $K$ divide $T$, partition the $T$ rounds into $K$ blocks of $T/K \ge N$ consecutive rounds, and let $H$ be a full-information algorithm with external regret at most $R_K$ over $K$ rounds on $[0,1]$ losses. In each block, play $H$'s current distribution, except that each arm is played once at an exploration time chosen uniformly at random in the block (distinct arms at distinct times), and give $H$ the observed exploration losses as the block's loss vector, whose expectation is the block-average loss vector. Then the expected loss is at most

$$
L_{\min}^T + NK + \frac{T}{K} R_K
$$

(Blum and Mansour, Section 4.6, display before Theorem 4.17). With an external regret procedure for which $R_K = O(\sqrt{K \log N})$ and $K = (T/N)^{2/3}$, for $T \ge N$, the expected loss is at most $L_{\min}^T + O(T^{2/3} N^{1/3} \log N)$ (Theorem 4.17).

## Proof sketch

The explored loss of arm $i$ in block $\tau$ has expectation equal to its block average, and $H$'s distribution for block $\tau$ depends only on explorations in earlier blocks, so in expectation the exploitation rounds behave like the block learner with regret $(T/K)R_K$. Exploration costs at most $N$ per block. With $R_K = O(\sqrt{K\log N})$ and $K = (T/N)^{2/3}$ the terms balance at order $T^{2/3}N^{1/3}\log N$.

Derived (not stated in the cited source): without the divisibility assumption, for $m \ge N$ and $K$ blocks of length $m$ with $Km \le T$, playing uniformly on the leftover $T - Km$ rounds gives expected loss at most $L_{\min}^T + NK + (T - Km) + mR$, where $R$ bounds $H$'s regret over $K$ rounds; the tail costs $T - Km < K$ when $m = \lfloor T/K \rfloor$. If, for every $K$, $H_K$ has regret at most $C\sqrt{K \ln N}$ with $C \ge 0$, then for $T \ge N$, $K = \lfloor (T/N)^{2/3} \rfloor$ and $m = \lfloor T/K \rfloor$ the expected loss is at most $L_{\min}^T + (3 + 2C)\, T^{2/3} N^{1/3} \ln N$.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)
- [Oblivious adversarial bandits](../../reinforcement-learning/multi-armed-bandits/oblivious-adversarial-bandits.md)

## Proof depends on

- [Block learner: running a full-information algorithm on block-averaged losses](block-full-information-learner.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4, Section 4.6 and Theorem 4.17.
