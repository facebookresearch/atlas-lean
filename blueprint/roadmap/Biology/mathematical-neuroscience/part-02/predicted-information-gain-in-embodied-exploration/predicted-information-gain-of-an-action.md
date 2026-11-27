# Predicted information gain of an action

In a controllable Markov chain with unknown kernel $\boldsymbol\Theta$ (prior $f$ under which the rows $\boldsymbol\Theta_{as\cdot}$ are independent, for example independent Dirichlet rows, so that the posterior stays a product; data $\vec d$; Bayesian estimate $\hat\Theta = \mathbb{E}[\boldsymbol\Theta\mid\vec d]$), let $\hat\Theta^{a,s\to s^*}$ be the Bayesian estimate after additionally observing the transition $s\to s^*$ under action $a$.

**Information gain** of that observation is the decrease in missing information:

$$\mathrm{IG}(a,s,s^*) = I_M(\Theta\,\|\,\hat\Theta) - I_M(\Theta\,\|\,\hat\Theta^{a,s\to s^*}) = \sum_{s'}\Theta_{ass'}\log_2\frac{\hat\Theta^{a,s\to s^*}_{ass'}}{\hat\Theta_{ass'}},$$

which the agent cannot compute because it depends on the true $\Theta$ and on the unknown outcome $s^*$. The second equality uses the row independence: the observation then changes no row of the estimate other than $(a,s)$. (The source draws its rows independently but does not state this hypothesis; for a prior tying rows together the gain is the sum of the KL terms over all rows that move.)

**Theorem (predicted information gain).** If the agent is in state $s$ with data $\vec d$, the expected information gain of action $a$ over the posterior of $\boldsymbol\Theta$ and the outcome $s^*$ is

$$\mathrm{PIG}(a,s) := \mathbb{E}_{s^*,\boldsymbol\Theta\mid\vec d}\big[\mathrm{IG}(a,s,s^*)\big] = \sum_{s^*}\hat\Theta_{ass^*}\,D_{\mathrm{KL}}\big(\hat\Theta^{a,s\to s^*}_{as\cdot}\,\big\|\,\hat\Theta_{as\cdot}\big).$$

PIG is computable from the agent's own model: imagine each outcome $s^*$, measure how far it would move the model (KL divergence), and average with the current predictive probabilities. A greedy explorer chooses $a = \arg\max_a \mathrm{PIG}(a,s)$ in its current state; because the agent is embodied (it can only act where it is), better strategies plan over future states using PIG as a reward.

## Expansion

Condition on $s^*$ first. Given $\vec d$ and $s^*$, the posterior mean of $\boldsymbol\Theta_{ass'}$ is $\hat\Theta^{a,s\to s^*}_{ass'}$, and the log ratio in IG does not depend on $\boldsymbol\Theta$, so the inner expectation becomes $D_{\mathrm{KL}}(\hat\Theta^{a,s\to s^*}_{as\cdot}\|\hat\Theta_{as\cdot})$. The outer average uses $p(s^*\mid a,s,\vec d) = \hat\Theta_{ass^*}$. The right-hand side had appeared earlier, ad hoc, as a model of human hypothesis testing; the theorem identifies it with the expected reduction in missing information.

## Depends on

- [Bayesian estimate minimizes expected missing information](bayesian-estimate-minimizes-expected-missing-information.md)

## Sources

- D. Y. Little, F. T. Sommer, *Learning and exploration in action-perception loops*, Frontiers in Neural Circuits 7 (2013), 37, Section 3.1 (Eqs. 6–7, Theorem 2), Section 3.3 (Eq. 9) and Appendix A3. <https://doi.org/10.3389/fncir.2013.00037> (PMCID: PMC3619626)
