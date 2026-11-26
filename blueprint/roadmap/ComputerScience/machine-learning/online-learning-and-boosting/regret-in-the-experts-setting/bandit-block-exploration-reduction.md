# Block-exploration reduction from bandit feedback to full information: regret $O(T^{2/3} N^{1/3} \ln N)$

In the partial-information (multi-armed bandit) experts model, an oblivious adversary fixes losses $\ell_t \in [0,1]^X$ for $N = |X| \ge 1$ arms, and the learner observes only the loss of the arm it plays.

Generic form: let $m \ge N$, $K$ blocks with $Km \le T$, and let $H$ be a full-information algorithm with external regret at most $R$ over $K$ rounds on $[0,1]$ losses. In each block, explore every arm once at a uniformly random collision-free position (so each arm's position is uniform in the block), use the observed losses as unbiased estimates of the block averages, play $H$'s distribution on the other $m - N$ rounds, and play uniformly on the leftover $T - Km$ rounds. Then the expected loss is at most $L_{\min}^T + NK + (T - Km) + mR$.

Tuned form: if, for every $K$, $H_K$ has regret at most $C\sqrt{K \ln N}$ with $C \ge 0$, then for $T \ge N$, $K = \lfloor (T/N)^{2/3} \rfloor$ and $m = \lfloor T/K \rfloor$, the expected loss is at most

$$
L_{\min}^T + (3 + 2C)\, T^{2/3} N^{1/3} \ln N .
$$

## Proof sketch

The explored loss of arm $i$ in block $\tau$ has expectation equal to its block average, and $H$'s distribution for block $\tau$ depends only on explorations in earlier blocks, so in expectation the exploitation rounds behave like the block learner with regret $mR$. Exploration costs at most $N$ per block and the tail at most $T - Km < K$. With $R = C\sqrt{K\ln N}$ and $K \approx (T/N)^{2/3}$ the three terms balance at order $T^{2/3}N^{1/3}$.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)
- [Oblivious adversarial bandits](../../reinforcement-learning/multi-armed-bandits/oblivious-adversarial-bandits.md)

## Proof depends on

- [Block learner: running a full-information algorithm on block-averaged losses](block-full-information-learner.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
