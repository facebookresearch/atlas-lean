# Law of large numbers for the reduced Othmer–Aldridge glycolysis model

**Setting.** The Othmer–Aldridge mechanism of the upper glycolytic pathway has ten species and sixteen reactions, involving fructose-6-phosphate $A_1$, ADP $A_2$, AMP $A_3$, ATP $A_4$ and the low-activity and activated forms of phosphofructokinase-1 and a second enzyme with their complexes. It is modelled as a continuous-time Markov chain on copy numbers with a scaling parameter $n$: the substrates $A_1, A_2, A_4$ are abundant (order $n$) and slow, while enzymes, complexes and $A_3$ are fast; $Z^n_S = n^{-1}(A_1,A_2,A_4)$ denotes the rescaled slow species. Write $K_1 = \kappa_{-7}\kappa_{-8}/(\kappa_7\kappa_8)$ for the ratio of rate constants of the adenylate reactions.

**Theorem.** Under the paper's scaling assumptions (moment bounds on the initial state and conserved enzyme totals of order one), $Z^n_S \Rightarrow (Z_{A_1}, Z_{A_2}, Z_{A_4})$ as $n\to\infty$, where $Z_{A_4}(t)\equiv Z_{A_4}(0)$ and $(Z_{A_1},Z_{A_2})$ has continuous paths solving the random ODE

$$\dot Z_{A_1} = \kappa_0 - f(Z_{A_1}, Z_{A_2}, Z_{A_4}(0)), \qquad \dot Z_{A_2} = f(Z_{A_1}, Z_{A_2}, Z_{A_4}(0)) - g(Z_{A_2}),$$

$$f(z_1,z_2,z_4) = \frac{1}{K_1 z_4 + z_2^2}\Big[\frac{V_1 K_1 z_1 z_4}{K_{M_1}+z_1} + \frac{V_1^{*} z_1 z_2^2}{K^{*}_{M_1}+z_1}\Big], \qquad g(z_2) = \frac{V_2 z_2}{K_{M_2}+z_2},$$

with positive constants $V_1, V_1^{*}, V_2$ (enzyme totals times catalytic rates) and Michaelis constants $K_{M_1}, K^{*}_{M_1}, K_{M_2}$. Moreover, the paper's trajectory-matching estimator of the identifiable reduced parameters from observations of $A_1$ and $A_2$ alone is consistent when the parameter space is compact.

## Expansion

The fast enzyme subsystem and AMP equilibrate on a faster time scale; their occupation measures converge to the stationary distribution of the fast dynamics given the slow state, and averaging the slow reaction rates against it gives Michaelis–Menten terms. The activated enzyme fraction is set by the adenylate equilibrium $2A_2 \rightleftharpoons A_3 + A_4$ and enzyme activation by AMP, which yields the factor $z_2^2/(K_1z_4+z_2^2)$ and the positive feedback of ADP that produces oscillations.

## Sources

- A. Ganguly, H.-W. Kang, "Stochastic averaging and statistical inference of glycolytic pathway", arXiv:2603.19577, Theorem 1 and Theorem 2. <https://doi.org/10.48550/arXiv.2603.19577>
