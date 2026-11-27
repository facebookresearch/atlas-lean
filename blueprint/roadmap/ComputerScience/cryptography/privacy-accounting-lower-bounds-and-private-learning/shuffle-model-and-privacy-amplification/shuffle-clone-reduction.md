# Shuffled local reports reduce to a binomial clone-counting problem

Let $R^{(1)}, \dots, R^{(n)}$ be local randomizers, where $R^{(i)}(z_{1:i-1}, \cdot)$ is $\varepsilon_0$-DP for all auxiliary inputs, and let $A_s(x_{1:n})$ sample a uniformly random permutation $\pi$ and output $z_i = R^{(i)}(z_{1:i-1}, x_{\pi(i)})$ for $i = 1, \dots, n$. Let $X_0, X_1$ be neighbouring datasets. Let $C \sim \mathrm{Bin}(n-1, e^{-\varepsilon_0})$, let $A$ given $C$ be distributed as $\mathrm{Bin}(C, 1/2)$ (so $A$ depends on $C$), and let $\Delta \sim \mathrm{Bern}\big(e^{\varepsilon_0}/(e^{\varepsilon_0}+1)\big)$ be independent of $(C, A)$. Then there is a randomized post-processing $\Phi$ such that

$$
A_s(X_0) \stackrel{d}{=} \Phi(A + \Delta,\; C - A + 1 - \Delta), \qquad A_s(X_1) \stackrel{d}{=} \Phi(A + 1 - \Delta,\; C - A + \Delta).
$$

Hence the privacy of the shuffled protocol is bounded by the indistinguishability of these two pairs of counts.

## Proof sketch

By the mixture decomposition, each of the other $n-1$ users independently, with probability $e^{-\varepsilon_0}$, produces a clone report distributed as an equal mixture of $Q(0)$ and $Q(1)$; the number of clones is $C$ and the number of clones choosing $Q(0)$ is $A$. The differing user's report is $Q(\Delta)$ or $Q(1-\Delta)$ according to the dataset. After shuffling, only the counts of $Q(0)$ and $Q(1)$ samples among the indistinguishable reports matter, so a post-processing $\Phi$ that samples the remaining non-clone reports and the $Q$-samples and shuffles them reproduces the output.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Every local randomizer is a mixture of a common component and two clones](local-randomizer-mixture-decomposition.md)

## Sources

- V. Feldman, A. McMillan, K. Talwar, "Hiding Among the Clones: A Simple and Nearly Optimal Analysis of Privacy Amplification by Shuffling", FOCS (2021), arXiv:2012.12803, Theorem 3.2.
