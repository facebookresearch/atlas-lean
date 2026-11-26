# Jump matrix of a rate matrix

Let $Q$ be a real square matrix indexed by a finite set $S$, with exit rates $q(i) = -Q(i, i)$. Its
jump matrix $\Pi$ is

$$\Pi(i, j) = \begin{cases} [i = j] & \text{if } q(i) = 0, \\ 0 & \text{if } q(i) \ne 0 \text{ and } j = i, \\ Q(i, j)/q(i) & \text{if } q(i) \ne 0 \text{ and } j \ne i : \end{cases}$$

a state with $q(i) = 0$ is absorbing.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press, 1997, Section 2.6.
