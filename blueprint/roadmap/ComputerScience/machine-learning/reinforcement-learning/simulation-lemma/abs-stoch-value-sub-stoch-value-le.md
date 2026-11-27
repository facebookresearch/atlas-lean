# Model accuracy gives value accuracy

Let $M$ and $\hat M$ be Markov decision processes on the same finite states $S$ and actions $A$, with the same rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$ and $\hat P(s,a,s')$, and let $0 \le \gamma < 1$. Assume the rewards lie in $[0,1]$ and $\sum_{s'} |P(s,a,s') - \hat P(s,a,s')| \le \varepsilon$ for all $s, a$. Then for every stochastic policy $\pi$ and state $s$,

$$|V^\pi(s) - \hat V^\pi(s)| \le \frac{\gamma \varepsilon}{(1-\gamma)^2}.$$

This is the value-accuracy step of model-based sample-complexity bounds with a generative model.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemmas 2.2 and 2.3 and the proof of Proposition 2.1

## Informally uses

- [Value bound](../stochastic-policies-and-discounted-occupancy/abs-mrp-value-le.md): the factor $1/(1-\gamma)$ from $(I - \gamma \hat P^\pi)^{-1}$.
