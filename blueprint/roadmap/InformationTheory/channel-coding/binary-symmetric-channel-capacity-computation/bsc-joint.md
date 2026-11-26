# Bsc Joint

Let $\delta \in [0, 1]$ and let $p$ be a probability distribution on $\{0, 1\}$. The joint law of input and output of the binary symmetric channel with crossover probability $\delta$ and input distribution $p$ is the probability distribution on $\{0, 1\} \times \{0, 1\}$ given by

$$P(x, y) = p(x) \cdot \begin{cases} 1 - \delta & \text{if } y = x, \\ \delta & \text{if } y \neq x. \end{cases}$$
