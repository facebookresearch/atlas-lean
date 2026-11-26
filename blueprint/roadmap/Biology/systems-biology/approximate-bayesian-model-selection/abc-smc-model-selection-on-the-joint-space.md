# ABC SMC model selection on the joint model–parameter space

Let $\mathcal{M} = \{1, \dots, |\mathcal{M}|\}$ index candidate models, with prior $P(m)$, parameter priors $P(\theta \mid m)$ and simulators $D \sim f(D \mid \theta, m)$. Fix observed data $D_0$, a distance $d$ and a tolerance $\epsilon \ge 0$. The **ABC target** on the joint space is

$$P_\epsilon(m, \theta \mid D_0) \propto P(m)\, P(\theta \mid m)\, \Pr\big(d(D_0, D^*) \le \epsilon \mid \theta, m\big), \qquad D^* \sim f(\cdot \mid \theta, m),$$

whose model marginal $P_\epsilon(m \mid D_0)$ approximates the posterior model probability $P(m \mid D_0) \propto P(D_0 \mid m) P(m)$ as $\epsilon \to 0$, and ratios $P_\epsilon(m_1 \mid D_0) P(m_2) / (P_\epsilon(m_2 \mid D_0) P(m_1))$ approximate Bayes factors.

**Rejection sampler.** Draw $m^* \sim P(m)$, $\theta^* \sim P(\theta \mid m^*)$, simulate $D^*$, and accept $(m^*, \theta^*)$ if $d(D_0, D^*) \le \epsilon$. With $N$ accepted particles, $\hat P(m \mid D_0) = \#\{\text{accepted particles with model } m\} / N$.

**Sequential Monte Carlo.** Choose tolerances $\epsilon_1 > \dots > \epsilon_T \ge 0$. Population $t = 1$ is drawn as above with weights $1$. For $t > 1$, each candidate is proposed by drawing $m^*$ with probability $P_{t-1}(m^*)$ (the current model marginal), perturbing it with a model kernel $m^{**} \sim KM_t(\cdot \mid m^*)$, drawing $\theta^*$ from the previous population's particles of model $m^{**}$ with their weights, and perturbing $\theta^{**} \sim KP_{t, m^{**}}(\cdot \mid \theta^*)$; candidates with zero prior density are discarded. A candidate is accepted with the indicator-average $b_t = \frac{1}{B_t}\sum_{r=1}^{B_t} \mathbf{1}\{d(D_0, D^*_r) \le \epsilon_t\}$ over $B_t$ replicate simulations (a candidate with $b_t = 0$ is rejected; $B_t = 1$ for deterministic models) and receives the importance weight

$$w_t(m^{**}, \theta^{**}) \propto \frac{P(m^{**})\, P(\theta^{**} \mid m^{**})\, b_t}{q_t(m^{**}, \theta^{**})}, \qquad q_t(m, \theta) = \Big[\sum_{m'} P_{t-1}(m')\, KM_t(m \mid m')\Big] \cdot \frac{\sum_{j : m_j = m} w^{(j)}_{t-1}\, KP_{t,m}(\theta \mid \theta^{(j)}_{t-1})}{\sum_{j : m_j = m} w^{(j)}_{t-1}},$$

where $q_t$ is the density of the proposal mechanism just described. After normalizing, the model marginal is $P_t(m) = \sum_{i : m^{(i)}_t = m} w^{(i)}_t$.

Properties:

- the weighted population at step $t$ targets $P_{\epsilon_t}(m, \theta \mid D_0)$; summing weights per model estimates its model marginal, and the parameter posteriors of each model are obtained from the same run;
- a model whose marginal reaches $0$ at some step is no longer proposed (unless the model kernel moves particles into it);
- with a uniform model prior and a discrete-uniform model kernel the algorithm reduces to ABC SMC parameter inference run on the augmented space.

## Expansion

The weight is the ratio of the (ABC-tilted) target density to the proposal density, the standard importance-sampling correction; $b_t$ is an unbiased estimate of the acceptance probability $\Pr(d \le \epsilon_t \mid \theta, m)$, which makes the algorithm valid for stochastic simulators. Annealing the tolerance lets each population serve as an informed proposal for the next, which is far cheaper than rejection sampling from the prior when parameter spaces are moderately high-dimensional. Applications include stochastic reaction kinetics, Gibbs random fields (where closed-form posteriors allow checking the approximation, and the cost is compared with ABC rejection), influenza household outbreak data and JAK-STAT signal transduction models; posterior model probabilities can be sensitive to model and parameter priors.

## Sources

- T. Toni and M. P. H. Stumpf, "Simulation-based model selection for dynamical systems in systems and population biology", Bioinformatics 26 (2010), Sections 1–2 ("ABC for model selection", "ABC SMC model selection algorithm on the joint space"), <https://doi.org/10.1093/bioinformatics/btp619> (PMC2796821).
