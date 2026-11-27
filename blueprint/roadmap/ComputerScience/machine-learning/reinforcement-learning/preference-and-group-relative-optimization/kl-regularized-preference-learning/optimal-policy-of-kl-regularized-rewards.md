# Optimal policy of KL-regularized reward maximization

For each prompt, the KL-regularized reward objective has a unique maximizer: the reference policy tilted by the exponentiated reward, $\pi_r(y \mid x) \propto \pi_{\mathrm{ref}}(y \mid x)\, e^{r(x,y)/\beta}$, which charges exactly the responses the reference policy charges.

Let $X$, $Y$, $\rho$, $r$, $\pi_{\mathrm{ref}}$, $\beta > 0$ and $J_\beta$ be as in [KL-regularized reward maximization](kl-regularized-reward-maximization.md). For each prompt $x$ put

$$Z(x) = \sum_{y \in Y} \pi_{\mathrm{ref}}(y \mid x)\, e^{r(x,y)/\beta}, \qquad \pi_r(y \mid x) = \frac{\pi_{\mathrm{ref}}(y \mid x)\, e^{r(x,y)/\beta}}{Z(x)}.$$

Then for every prompt $x$ and every probability distribution $\delta$ on $Y$,

$$\mathbb{E}_{y \sim \delta}\, r(x,y) - \beta\, \mathrm{KL}\bigl(\delta \,\|\, \pi_{\mathrm{ref}}(\cdot \mid x)\bigr) = \beta \log Z(x) - \beta\, \mathrm{KL}\bigl(\delta \,\|\, \pi_r(\cdot \mid x)\bigr),$$

both sides being $-\infty$ when $\delta$ charges a response outside the support of $\pi_{\mathrm{ref}}(\cdot \mid x)$. Hence $\pi_r(\cdot \mid x)$ is the unique maximizer of the per-prompt objective on the left, with maximal value $\beta \log Z(x)$, and a policy $\pi$ maximizes $J_\beta$ if and only if $\pi(\cdot \mid x) = \pi_r(\cdot \mid x)$ for every prompt $x$ with $\rho(x) > 0$. Moreover $\pi_r(y \mid x) > 0$ if and only if $\pi_{\mathrm{ref}}(y \mid x) > 0$.

## Depends on

- [KL-regularized reward maximization](kl-regularized-reward-maximization.md)
- [Kullback–Leibler divergence on a finite space](../../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Proof depends on

- [Gibbs variational principle](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/is-greatest-integral-sub-kl-div.md)
- [Cross-entropy is entropy plus divergence](../../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/cross-entropy-eq-shannon-entropy-add-kl.md)
- [Equality in Gibbs' inequality](../../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/cross-entropy-eq-shannon-entropy-iff.md)

## Expansion

Fix $x$ and a distribution $\delta$ supported in the support of $\pi_{\mathrm{ref}}(\cdot \mid x)$. Dividing by $\beta$ and collecting logarithms,

$$\sum_y \delta(y)\Bigl(\frac{r(x,y)}{\beta} - \log\frac{\delta(y)}{\pi_{\mathrm{ref}}(y \mid x)}\Bigr) = \sum_y \delta(y) \log\frac{\pi_r(y \mid x)\, Z(x)}{\delta(y)} = \log Z(x) - \mathrm{KL}\bigl(\delta \,\|\, \pi_r(\cdot \mid x)\bigr),$$

which is the identity. The partition function $Z(x)$ depends on $x$, $r$ and $\pi_{\mathrm{ref}}$ but not on $\delta$, so maximizing the left side means minimizing $\mathrm{KL}(\delta \,\|\, \pi_r(\cdot \mid x))$, which is nonnegative and vanishes only at $\delta = \pi_r(\cdot \mid x)$ (Gibbs' inequality and its equality case). On the finite set $Y$ this is the Gibbs variational principle for the base measure $\pi_{\mathrm{ref}}(\cdot \mid x)$ and the bounded function $r(x,\cdot)/\beta$, multiplied by $\beta$. Because the objective $J_\beta$ averages the per-prompt objectives with weights $\rho(x)$, a policy is optimal exactly when it is optimal at every prompt of positive probability; at prompts with $\rho(x) = 0$ it is unconstrained.

Rafailov et al. observe that $Z(x)$ is expensive to evaluate when $Y$ is large, which is why the closed form is not used directly. The same closed form, with reward $g(x,y) = \mathbb{E}_{y' \sim \mu(\cdot \mid x)} \Psi(p^*(y \succ y' \mid x))$, gives the closed-form optimum of [Ψ-preference optimization](psi-preference-optimization.md).

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Section 4, equation (4), and Appendix A.1 of the supplementary material (derivation via Gibbs' inequality). [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Appendix A.1 (existence and uniqueness of the regularized argmaximum, with the identity above for a finite set) and equation (7). [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
