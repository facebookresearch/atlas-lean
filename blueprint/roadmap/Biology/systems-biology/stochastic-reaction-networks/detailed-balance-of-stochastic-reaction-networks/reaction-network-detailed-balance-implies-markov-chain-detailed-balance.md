# Reaction network detailed balance implies Markov chain detailed balance

**Setting.** A reversible chemical reaction network $(\mathcal S, \mathcal C, \mathcal R)$ with mass-action kinetics has a deterministic (ODE) model and a stochastic (continuous-time Markov chain) model on $\mathbb Z^{s}_{\ge 0}$. For a reaction vector $\mathbf u$, let $\mathcal R(\mathbf u) = \{\mathbf y_i(\mathbf u) \xrightarrow{k_i(\mathbf u)} \mathbf y_i(\mathbf u) + \mathbf u : 1 \le i \le r(\mathbf u)\}$ be the $r(\mathbf u)$ reactions sharing that vector. *Reaction network detailed balance* (RNDB) means there is a positive steady state of the ODE at which every reaction is balanced by its reverse. *Markov chain detailed balance* (MCDB) means the CTMC on each irreducible class satisfies $\pi(x)q(x,y) = \pi(y)q(y,x)$ for some positive $\pi$.

**Theorem.**
1. *(Rate conditions for RNDB.)* The network has RNDB iff (i) for every reaction vector $\mathbf u$,

$$\frac{k_1(\mathbf u)}{k_1(-\mathbf u)} = \cdots = \frac{k_{r(\mathbf u)}(\mathbf u)}{k_{r(\mathbf u)}(-\mathbf u)},$$

and (ii) for every reaction cycle $(\mathbf u_1, \dots, \mathbf u_c)$ (reaction vectors with $\sum_i \mathbf u_i = \mathbf 0$) and every choice of indices $q(\mathbf u_i) \in \{1, \dots, r(\mathbf u_i)\}$, $\prod_{i=1}^c k_{q(\mathbf u_i)}(\mathbf u_i)/k_{q(\mathbf u_i)}(-\mathbf u_i) = 1$.
2. *(Sufficiency.)* If a reversible network has RNDB, its stochastic mass-action model has MCDB.
3. *(Coincidence.)* If $r(\mathbf u) = 1$ for every reaction vector, RNDB and MCDB are equivalent.
4. *(Not necessary in general.)* For $2A \rightleftharpoons A + B \rightleftharpoons 2B$, RNDB requires $k_2/k_{-2} = k_3/k_{-3}$, whereas MCDB holds for all rate constants.

## Expansion

RNDB is equivalent to Whittle's stochastic detailed balance, which gives a product-form Poisson stationary law; the Kolmogorov cycle criterion then verifies MCDB for the chain. The converse fails because the Markov chain only sees transitions between molecule counts: in the example both reactions have reaction vector $\pm(-1, 1)$, each conservation class $\{a + b = n\}$ is a line, and every birth–death chain on a line is reversible, so no rate condition is needed. When each reaction vector belongs to a single reaction, distinct transitions of the chain correspond to distinct reactions and the two cycle conditions coincide.

## Sources

- Badal Joshi, "A detailed balanced reaction network is sufficient but not necessary for its Markov chain to be detailed balanced", Discrete and Continuous Dynamical Systems - B 20 (2015), 1077–1105, <https://doi.org/10.3934/dcdsb.2015.20.1077>; numbering as in arXiv:1312.4196: Theorems 4.3, 5.9 and 5.10 and Table 1 (Section 2).
