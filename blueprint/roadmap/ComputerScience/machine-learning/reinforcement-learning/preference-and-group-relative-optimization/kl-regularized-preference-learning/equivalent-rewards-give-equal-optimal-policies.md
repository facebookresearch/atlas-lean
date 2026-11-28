# Equivalent rewards induce the same KL-regularized optimal policy

Two equivalent rewards have the same optimal policy under KL-regularized reward maximization: shifting the reward by a function of the prompt only rescales the partition function.

Let $X$ and $Y$ be finite, $\pi_{\mathrm{ref}}$ a reference policy and $\beta > 0$, and let $r'(x,y) = r(x,y) + f(x)$ be [equivalent](equivalent-reward-functions.md) to $r$. Then the [optimal policies of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md) for the two rewards coincide:

$$\pi_{r'}(y \mid x) = \pi_r(y \mid x) \qquad \text{for all } x \in X,\ y \in Y.$$

## Depends on

- [Equivalent reward functions](equivalent-reward-functions.md)
- [Optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)

## Proof depends on

None.

## Expansion

With $Z_r(x) = \sum_y \pi_{\mathrm{ref}}(y \mid x) e^{r(x,y)/\beta}$ one has $Z_{r'}(x) = e^{f(x)/\beta} Z_r(x)$, and the factor $e^{f(x)/\beta}$ cancels in $\pi_{r'}(y \mid x) = \pi_{\mathrm{ref}}(y \mid x) e^{r'(x,y)/\beta}/Z_{r'}(x)$. Equivalently, the objectives differ by the policy-independent constant $\mathbb{E}_{x \sim \rho} f(x)$. For the final objective of direct preference optimization only the class of the reward matters, so it suffices to recover any member of the optimal class.

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Lemma 2 (Section 5.1), with proof in Appendix A.5 of the supplementary material. [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
