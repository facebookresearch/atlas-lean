# Hybrid model-based and model-free control in the two-step task

**Task.** On each trial $t$ an agent chooses an action $a_{1,t}$ in the first-stage state $s_A$, moves to one of two second-stage states $s_B, s_C$ according to transition probabilities $P(s' \mid s_A, a)$, chooses an action $a_{2,t}$ there, and receives reward $r_{2,t}$ (the first-stage reward $r_{1,t}$ is $0$). Second-stage reward probabilities drift slowly.

**Model-free learner (SARSA($\lambda$)).** Values $Q_{\mathrm{MF}}(s, a)$ are updated by

$$Q_{\mathrm{MF}}(s,a) \leftarrow Q_{\mathrm{MF}}(s,a) + \alpha\,\delta_{i,t}\,e_{i,t}(s,a), \qquad \delta_{i,t} = r_{i,t} + Q_{\mathrm{MF}}(s_{i+1,t}, a_{i+1,t}) - Q_{\mathrm{MF}}(s_{i,t}, a_{i,t}),$$

with learning rate $\alpha$ and eligibility traces reset to $0$ at each trial, incremented by $1$ for the visited pair and decayed by $\lambda$ after each update. In the two-step task this gives $\delta_{1,t} = Q_{\mathrm{MF}}(s_{2,t}, a_{2,t}) - Q_{\mathrm{MF}}(s_{1,t}, a_{1,t})$ and $\delta_{2,t} = r_{2,t} - Q_{\mathrm{MF}}(s_{2,t}, a_{2,t})$, the first-stage value receiving the second-stage error weighted by $\lambda$.

**Model-based learner.** Second-stage values coincide with model-free ones, and first-stage values are computed by the Bellman equation

$$Q_{\mathrm{MB}}(s_A, a_j) = P(s_B \mid s_A, a_j)\max_{a} Q_{\mathrm{MF}}(s_B, a) + P(s_C \mid s_A, a_j)\max_{a} Q_{\mathrm{MF}}(s_C, a).$$

**Hybrid choice rule.** First-stage values are mixed with weight $w \in [0,1]$,

$$Q_{\mathrm{net}}(s_A, a_j) = w\,Q_{\mathrm{MB}}(s_A, a_j) + (1 - w)\,Q_{\mathrm{MF}}(s_A, a_j),$$

and choices at both stages follow the softmax rule

$$P(a_{i,t} = a \mid s_{i,t}) = \frac{\exp\big(\beta Q_{\mathrm{net}}(s_{i,t}, a)\big)}{\sum_{a'} \exp\big(\beta Q_{\mathrm{net}}(s_{i,t}, a')\big)},$$

with inverse temperature $\beta$ ($Q_{\mathrm{net}} = Q_{\mathrm{MF}}$ at the second stage); $\beta \to \infty$ gives greedy choice and $\beta \to 0$ uniform choice.

**Finding.** In the original two-step task (reward probabilities following Gaussian random walks with $\sigma = 0.025$ reflected at $0.25$ and $0.75$), simulated reward rate depends only weakly on $w$ across learning rates and temperatures, so the task embodies no accuracy–demand trade-off between the two systems. Five factors limit the benefit of model-based control: poorly distinguishable second-stage reward probabilities, slow drift, probabilistic transitions, a second-stage choice, and low informativeness of each reward observation. Changing all five (wider reward range, faster drift, deterministic transitions, a single second-stage option, more informative rewards) is required, superadditively, to obtain a reliable positive relation between $w$ and reward.

## Expansion

The model-free learner caches values and needs repeated experience to propagate a change in second-stage reward back to the first stage, at a rate set by $\alpha$ and $\lambda$. The model-based learner propagates such changes immediately through the transition model, which helps only if second-stage values differ enough and change fast enough for the first-stage choice to matter; with probabilistic transitions and slowly drifting rewards confined to $[0.25, 0.75]$ these conditions fail, which is why $w$ barely affects earnings. Fitting $(\alpha, \beta, \lambda, w)$ by maximum likelihood to choices yields $w$ as a behavioral index of model-based control.

## Sources

- W. Kool, F. A. Cushman, S. J. Gershman, "When does model-based control pay off?", PLoS Computational Biology 12(8) (2016) e1005090, Methods (model-free strategy, model-based strategy, decision rule, simulation of the accuracy–demand trade-off), <https://doi.org/10.1371/journal.pcbi.1005090> (PMC5001643).
- N. D. Daw, S. J. Gershman, B. Seymour, P. Dayan, R. J. Dolan, "Model-based influences on humans' choices and striatal prediction errors", Neuron 69 (2011) 1204–1215.
