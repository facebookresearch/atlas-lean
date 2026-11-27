# Group-relative advantage

Group relative policy optimization (GRPO) scores a sampled response by its reward standardized with the mean and standard deviation of rewards for the same prompt, computed either exactly under the sampling policy or from a group of sampled responses.

Let $X$ be a set of prompts, $Y$ a set of responses, $r : X \times Y \to \mathbb{R}$ a reward, $\alpha$ a sampling policy (the current policy or an earlier one) and $\varepsilon > 0$ a constant. The **population group-relative advantage** is

$$A_\alpha(x,y) = \frac{r(x,y) - \mu_{\alpha,r}(x)}{\sigma_{\alpha,r,\varepsilon}(x)}, \qquad \mu_{\alpha,r}(x) = \mathbb{E}_{y \sim \alpha(\cdot \mid x)} r(x,y), \quad \sigma_{\alpha,r,\varepsilon}(x) = \sqrt{\sigma_{\alpha,r}(x)^2 + \varepsilon},$$

where $\sigma_{\alpha,r}(x)^2 = \mathbb{E}_{y \sim \alpha(\cdot \mid x)}(r(x,y) - \mu_{\alpha,r}(x))^2$. Its **group estimate** draws $G$ responses $y_1, \dots, y_G$ independently from $\alpha(\cdot \mid x)$, sets $r_i = r(x, y_i)$, and uses

$$\hat A_i = \frac{r_i - \bar r}{\sqrt{s^2 + \varepsilon}}, \qquad \bar r = \frac{1}{G} \sum_{j=1}^{G} r_j,$$

with $s$ the empirical standard deviation of $r_1, \dots, r_G$. The original GRPO formulation takes $\varepsilon = 0$, $\hat A_i = (r_i - \bar r)/s$, and in outcome supervision assigns $\hat A_i$ to every token of response $y_i$. The sources do not fix whether $s^2$ divides by $G$ or by $G - 1$.

## Depends on

None.

## Proof depends on

None.

## Expansion

The centred rewards sum to zero, $\sum_i (r_i - \bar r) = 0$, hence $\sum_i \hat A_i = 0$; group-based objectives often work with the centred advantage $r_i - \bar r$ and move the factor $1/s$ into per-response weights. In a zero-variance group, $r_1 = \dots = r_G$, every centred reward vanishes: with $\varepsilon > 0$ every $\hat A_i$ is $0$, while with $\varepsilon = 0$ the quotient is $0/0$ and needs a convention, either setting it to $0$ or discarding the prompt. Mroueh et al. mask prompts whose population variance under the current policy is zero, and note that masking on the variance estimated from a finite group introduces a bias, especially for small $G$.

$\hat A_i$ is a plug-in estimate that substitutes sample statistics for $\mu_{\alpha,r}$ and $\sigma_{\alpha,r}$; it is a different random quantity from $A_\alpha(x, y_i)$, and none of the sources cited here claims that $\hat A_i$, or a policy-gradient estimate formed with it, is unbiased for the corresponding population quantity. The [GRPO policy improvement lower bound](grpo-policy-improvement-lower-bound.md) is stated for the population advantage $A_\alpha$.

## Sources

- Y. Mroueh, N. Dupuis, B. Belgodere, A. Nitsure, M. Rigotti, K. Greenewald, J. Navratil, J. Ross and J. Rios, *Revisiting Group Relative Policy Optimization: Insights into On-Policy and Off-Policy Training*, International Conference on Learning Representations (ICLR 2026), Section 2, Section 3, equation (2), equation (7) and Remark 1 (zero-variance masking and its bias). [PDF](https://proceedings.iclr.cc/paper_files/paper/2026/file/b4008025c2182bfe16fcc8566ee14d64-Paper-Conference.pdf)
- Z. Shao, P. Wang, Q. Zhu, R. Xu, J. Song, X. Bi, H. Zhang, M. Zhang, Y. K. Li, Y. Wu and D. Guo, *DeepSeekMath: Pushing the Limits of Mathematical Reasoning in Open Language Models*, preprint, arXiv:2402.03300v3, Section 4.1.2 (outcome supervision).
- A. Fontana, M. Simoni, G. Rossolini, P. Mori and A. Saracino, *On the Hidden Objective Biases of Group-based Reinforcement Learning*, Proceedings of the 64th Annual Meeting of the Association for Computational Linguistics (Volume 2: Short Papers), ACL 2026, pages 109–121, Section 3, equation (2) and Table 1. [publisher page](https://aclanthology.org/2026.acl-short.11/)
