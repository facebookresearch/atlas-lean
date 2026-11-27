# Shifted Hill circuit model and its invariant box

For a regulatory link from gene $j$ to gene $i$ with threshold $x^0_{ji} > 0$, Hill coefficient $n_{ji} \in \mathbb{N}$ and maximal fold change $\lambda_{ji} \ge 0$ ($\lambda_{ji} > 1$ for activation, $0 \le \lambda_{ji} < 1$ for inhibition), define the shifted Hill function

$$H^S_{ji}(x) \;=\; \lambda_{ji} + (1 - \lambda_{ji})\,\frac{1}{1 + (x/x^0_{ji})^{n_{ji}}}, \qquad x \ge 0 .$$

It satisfies $H^S_{ji}(0) = 1$, $H^S_{ji}(x) \to \lambda_{ji}$ as $x \to \infty$, and is monotone (increasing for activation, decreasing for inhibition). A circuit on genes $1, \dots, N$ with regulator sets $\mathcal R_i$ is modelled by

$$\dot X_i \;=\; g_i \prod_{j \in \mathcal R_i} H^S_{ji}(X_j) \;-\; k_i X_i, \qquad g_i, k_i > 0,$$

with basal production rate $g_i$ and degradation rate $k_i$. For example, the toggle switch is $\dot A = g_A H^S_{BA}(B) - k_A A$, $\dot B = g_B H^S_{AB}(A) - k_B B$ with both links inhibitory. Let

$$m_i = g_i \prod_{j \in \mathcal R_i} \min(1, \lambda_{ji}), \qquad G_i = g_i \prod_{j \in \mathcal R_i} \max(1, \lambda_{ji}) .$$

$G_i$ is the maximal production rate of gene $i$. RACIPE samples $G_i$ in a common range and sets $g_i = G_i/\prod_j \max(1, \lambda_{ji})$, so that all genes share the same scale of maximal production.

**Auxiliary properties** (derived here, not stated in the source; proved in the Expansion). For every initial condition in $[0, \infty)^N$:

1. the box $\mathcal B = \prod_i [m_i/k_i,\ G_i/k_i]$ is forward invariant;
2. $\operatorname{dist}(X_i(t), [m_i/k_i, G_i/k_i]) \le e^{-k_i t}\operatorname{dist}(X_i(0), [m_i/k_i, G_i/k_i])$, so $\mathcal B$ attracts all trajectories exponentially;
3. every equilibrium lies in $\mathcal B$, and at least one exists.

## Depends on

- [Hill repression function](../../genetic-toggle-switch/hill.md)

## Expansion

Each factor $H^S_{ji}(x)$ is a convex combination of $1$ and $\lambda_{ji}$ with weight $1/(1 + (x/x^0)^n) \in (0, 1]$, so it lies between $\min(1,\lambda_{ji})$ and $\max(1,\lambda_{ji})$. Hence the production term $P_i(X)$ satisfies $m_i \le P_i(X) \le G_i$ on the nonnegative orthant. If $X_i > G_i/k_i$ then $\frac{d}{dt}(X_i - G_i/k_i) \le -k_i(X_i - G_i/k_i)$, and symmetrically below $m_i/k_i$. Grönwall's inequality gives item 2, and items 1 and 3 follow, with existence of an equilibrium from Brouwer's fixed-point theorem applied to $X \mapsto (P_i(X)/k_i)_i$, a continuous map of $\mathcal B$ into itself. In the RACIPE protocol, Hill coefficients are integers from $1$ to $6$, degradation rates lie in $[0.1, 1]$, $G_i \in [1, 100]$, activation fold changes $\lambda^+ \in [1, 100]$, and inhibition fold changes are sampled through $1/\lambda^-$ so that strong repression is common. Thresholds follow the half-functional rule: each is drawn from $[0.02M, 1.98M]$, where $M$ is the median steady-state level of the regulator estimated from a random ensemble, so that every link is active in roughly half of the models. The stable states found across thousands of models then cluster into the circuit's robust phenotypes, such as the two states of the toggle switch.

## Sources

- B. Huang, M. Lu, D. Jia, E. Ben-Jacob, H. Levine, J. N. Onuchic, "Interrogating the topological robustness of gene regulatory circuits by randomization", *PLoS Computational Biology* 13(3) (2017) e1005456, Methods (Equations (1)–(2), parameter randomization, the half-functional rule) and Results, "RACIPE as an unbiased method to predict robust gene states for a gene circuit", <https://doi.org/10.1371/journal.pcbi.1005456> (PMC5391964). The source defines the model and makes no claim about invariant or attracting regions; the auxiliary properties are the page's own comparison and fixed-point argument.
