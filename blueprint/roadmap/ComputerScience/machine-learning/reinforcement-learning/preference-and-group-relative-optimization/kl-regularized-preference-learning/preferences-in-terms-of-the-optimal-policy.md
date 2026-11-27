# Preference probabilities in terms of the optimal policy

If preferences follow the Bradley–Terry model with reward $r^*$, they can be written using only the KL-regularized optimal policy $\pi^*$ of $r^*$ and the reference policy, because the partition function cancels.

Let $X$ and $Y$ be finite, $\pi_{\mathrm{ref}}$ a reference policy, $\beta > 0$, $r^*$ a reward, and $\pi^* = \pi_{r^*}$ the [optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md) for $r^*$. Suppose the preference distribution follows the [Bradley–Terry model](bradley-terry-and-plackett-luce-models.md) with reward $r^*$, $p^*(y_1 \succ y_2 \mid x) = \sigma(r^*(x,y_1) - r^*(x,y_2))$. Then for every prompt $x$ and all responses $y_1, y_2$ with $\pi_{\mathrm{ref}}(y_1 \mid x) > 0$ and $\pi_{\mathrm{ref}}(y_2 \mid x) > 0$,

$$p^*(y_1 \succ y_2 \mid x) = \sigma\Bigl(\beta \log \frac{\pi^*(y_1 \mid x)}{\pi_{\mathrm{ref}}(y_1 \mid x)} - \beta \log \frac{\pi^*(y_2 \mid x)}{\pi_{\mathrm{ref}}(y_2 \mid x)}\Bigr).$$

Likewise, if $p^*$ follows the Plackett–Luce model with reward $r^*$, then for responses $y_1, \dots, y_K$ in the support of $\pi_{\mathrm{ref}}(\cdot \mid x)$ and every ranking $\tau$, $p^*(\tau \mid y_1, \dots, y_K, x)$ is the Plackett–Luce probability computed with the rewards $\beta \log\bigl(\pi^*(y_{\tau(k)} \mid x)/\pi_{\mathrm{ref}}(y_{\tau(k)} \mid x)\bigr)$ in place of $r^*(x, y_{\tau(k)})$.

## Depends on

- [Bradley–Terry and Plackett–Luce preference models](bradley-terry-and-plackett-luce-models.md)
- [Optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)

## Proof depends on

None.

## Expansion

On the support of $\pi_{\mathrm{ref}}(\cdot \mid x)$ the closed form of $\pi^*$ gives $r^*(x,y) = \beta \log(\pi^*(y \mid x)/\pi_{\mathrm{ref}}(y \mid x)) + \beta \log Z(x)$. The Bradley–Terry and Plackett–Luce probabilities depend only on reward differences between responses to the same prompt, so the term $\beta \log Z(x)$ cancels. The expressions are maximum-likelihood objectives for a policy instead of a reward, which is the step from reward modeling to the [DPO loss](direct-preference-optimization-loss.md).

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Section 4, equations (5) and (6), and Appendices A.2 and A.3 of the supplementary material (Bradley–Terry and Plackett–Luce derivations). [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
