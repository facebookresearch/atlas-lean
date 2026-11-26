# Expected cumulative reward to reach a target

Let $M$ be a [Markov decision process](markov-decision-processes-and-adversaries.md) with a [reward structure](reward-structures.md) $r$, let $T \subseteq S$ be a set of target states and $s \in S$. The random variable $F^T_r$ on the infinite paths $\pi = s_0 \xrightarrow{a_0} s_1 \xrightarrow{a_1} \cdots$ from $s$ is

$$F^T_r(\pi) = \begin{cases} \infty & \text{if } s_i \notin T \text{ for all } i \in \mathbb{N}, \\ \sum_{i=0}^{k^T_\pi - 1} \bigl( r_{\mathrm{state}}(s_i) + r_{\mathrm{action}}(s_i, a_i) \bigr) & \text{otherwise,} \end{cases}$$

with $k^T_\pi = \min\{k \mid s_k \in T\}$. The minimum and maximum expected cumulative rewards to reach $T$ are $E^{\min}_s(F^T_r) = \inf_\sigma E^\sigma_s(F^T_r)$ and $E^{\max}_s(F^T_r) = \sup_\sigma E^\sigma_s(F^T_r)$ over all adversaries $\sigma$, where $E^\sigma_s$ is the expectation under $\Pr^\sigma_{M,s}$. Deterministic memoryless adversaries attain both, and $E^{\min}_s(F^T_r)$ is infinite exactly when every adversary reaches $T$ from $s$ with probability less than $1$.

## Depends on

- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)
- [Reward structures](reward-structures.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 5.3.
