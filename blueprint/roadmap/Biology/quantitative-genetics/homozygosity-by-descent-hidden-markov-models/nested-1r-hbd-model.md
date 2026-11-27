# Nested 1R model for homozygosity by descent from layers of ancestors

Fix $L$ layers of ancestors with rates $0 = R_0 < R_1 < R_2 < \dots < R_L$ and mixing coefficients $\rho_1,\dots,\rho_L \in (0,1)$. Layer $c$ is a [1R model](single-class-hbd-hidden-markov-model.md) with parameters $(R_c,\rho_c)$ applied to the positions that are non-HBD in layers $1,\dots,c-1$. The hidden states are $c = 1,\dots,L$ (HBD in layer $c$) and $K = L+1$ (non-HBD in every layer); HBD emissions are as in the 1R model for every class and the state-$K$ emission is the Hardy–Weinberg one.

**Transition matrix.** For markers $m, m+1$ at distance $d_m$, set $R_{K} := R_L$ and

$$\chi_c^m = e^{-R_{c-1}d_m} - e^{-R_cd_m}, \qquad c = 1,\dots,L,$$

the probability that the first coancestry change (going back in time) falls in layer $c$; then $\sum_{i=1}^c \chi_i^m = 1 - e^{-R_cd_m}$. Let $T_0^m = \operatorname{diag}(e^{-R_1d_m},\dots,e^{-R_Ld_m},e^{-R_Ld_m})$, let $T_\chi^m$ be the $L\times K$ matrix with $T_\chi^m(c,c') = \chi_c^m$ if $c \le c'$ and $0$ otherwise, and let $T_C$ be the $L\times K$ matrix of conditional destinations after a first change in layer $c$:

$$T_C(c,c') = \begin{cases} 0 & c' < c,\\ \rho_c & c' = c,\\ \Big[\prod_{j=c}^{c'-1}(1-\rho_j)\Big]\rho_{c'} & c < c' \le L,\\ \prod_{j=c}^{L}(1-\rho_j) & c' = K.\end{cases}$$

Then the transition matrix is

$$T^m = T_0^m + (T_\chi^m)^\top T_C .$$

**Initial distribution and stationarity.** With $\delta$ the first row of $T_C$,

$$\delta_c = \Big[\prod_{j=1}^{c-1}(1-\rho_j)\Big]\rho_c \ (c \le L), \qquad \delta_K = \prod_{j=1}^L (1-\rho_j),$$

one has $\delta T^m = \delta$ for every $m$: the chain is stationary, so at every marker the probability of HBD class $c$ is $\delta_c$, and $\delta_c$ is the expected fraction of markers in class $c$. Hence the **expected** inbreeding with respect to ancestors up to layer $c$, the expected fraction of markers in classes $1, \dots, c$, is $\sum_{i \le c}\delta_i = 1 - \prod_{j=1}^c(1-\rho_j)$, so the $\rho_c$ keep the interpretation of inbreeding coefficients, unlike in the earlier multiple-rate (MixKR) model. The **realized** fraction of a given genome in those classes is a random variable (at a single marker it is $0$ or $1$); it is estimated from the local state posteriors, as the average over markers of the posterior probability of classes $1, \dots, c$. For $L = 1$ the model is the 1R model.

## Depends on

- [Single-class homozygous-by-descent hidden Markov model (1R model)](single-class-hbd-hidden-markov-model.md)

## Proof depends on

None beyond multiplying out $\delta T^m$ with the telescoping identity $\sum_{i=1}^c \chi_i^m = 1 - e^{-R_cd_m}$, as the Expansion describes.

## Expansion

From state $c'$ either no coancestry change happens in layers $1,\dots,\min(c',L)$ (probability $e^{-R_{c'}d_m}$, the diagonal term), or the first change happens in some layer $c \le c'$ (probability $\chi_c^m$), after which the destination is drawn down the decision tree "HBD in layer $c$ with probability $\rho_c$, else pass to layer $c+1$", which is $T_C(c,\cdot)$. Stationarity follows from the self-similar structure: the destination law after a change in layer $c$ is $\delta$ conditioned on being non-HBD in layers $<c$, which balances the outflow.

## Sources

- Tom T. Druet and Mathieu Gautier, "A hidden Markov model to estimate homozygous-by-descent probabilities associated with nested layers of ancestors", Theoretical Population Biology (2022), <https://doi.org/10.1016/j.tpb.2022.03.001>. bioRxiv 10.1101/2021.05.25.445246. Section 2.2, Eqs. (5)–(15) and Appendix (stationarity).
