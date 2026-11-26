# RAF phase transitions under heterogeneous random catalysis

**Setting.** In Kauffman's polymer model over an alphabet of size $\kappa\ge2$, the molecule set $X_n$ consists of all strings of length at most $n$, and the forward reactions $R_n^+$ are ligations of two strings into their concatenation (with the reverse cleavages). The food set $F=X_t$ is all strings of length at most a fixed $t$. A catalytic reaction system is **RAF** (reflexively autocatalytic and food-generated) if it contains a nonempty set of reactions each catalysed by some molecule produced from $F$ by that set, every reactant being likewise producible. In the **weighted random catalysis model**, each molecule $x$ carries an i.i.d. activity $W_x\in(0,\infty)$; given the weights, the indicators that $x$ catalyses $r$ are independent with

$$\mathbb P(I_{x,r}=1\mid W)=1-\exp\{-\lambda_nW_xK_n(x,r)\},$$

for an intensity $\lambda_n\ge0$ and a compatibility kernel $K_n\ge0$. The **weighted catalytic mass** of a reaction is $M_n(r)=\sum_{x\in X_n}K_n(x,r)W_x$, and $\mathcal B_t$ is the set of forward reactions whose reactants all lie in $F$.

**Theorem 1 (weighted catalytic mass criterion).** For arbitrary i.i.d. positive finite weights:
1. if $\lambda_n\max_{r\in\mathcal B_t}M_n(r)\to0$ in probability, then $\mathbb P_n(\mathrm{RAF})\to0$;
2. if $\lambda_n\min_{r\in R_n^+}M_n(r)\to\infty$ in probability, then $\mathbb P_n(\mathrm{RAF})\to1$.

**Theorems 7 and 8 (Pareto activities).** Let $W$ be Pareto with tail index $\alpha$ and the kernel reaction-independent, $K_n(x,r)=k_n(x)$. For $0<\alpha<1$ (infinite mean), with $A_n^{(\alpha)}=\lambda_n^\alpha\sum_xk_n(x)^\alpha$: $A_n^{(\alpha)}\to0$ implies $\mathbb P_n(\mathrm{RAF})\to0$ and $A_n^{(\alpha)}\to\infty$ implies $\mathbb P_n(\mathrm{RAF})\to1$. At $\alpha=1$, with $\lambda_n\to0$ and bounded total kernel mass, the same dichotomy holds for $A_n^{(1)}=\lambda_n\sum_xk_n(x)\log\bigl(1/(\lambda_nk_n(x))\bigr)$. For $\alpha>1$ (finite mean) the threshold is on $\lambda_n$ itself (Proposition 6).

**Proposition 9 (a single catalyst suffices).** With Pareto activities of any index $\alpha$, if $\lambda_n^\alpha N_n^{1-\alpha}/(\log N_n)^\alpha\to\infty$ (for the paper's uniform-kernel setting with $N_n$ molecules), then with probability tending to one there is a nonempty food-generated RAF all of whose reactions are catalysed by one and the same molecule.

## Expansion

If every food-reactant reaction has vanishing expected number of catalysts, no first catalysed step exists and no RAF can start; this is the subcritical half, needing only reactions in $\mathcal B_t$. If every reaction has diverging catalytic mass, then with high probability the whole system is catalysed and the full reaction set is an RAF. Conditioning on weights reduces both to Poisson-type bounds with rate $\lambda_nM_n(r)$. With heavy-tailed activities, $M_n$ is dominated by its largest summands, so $\lambda_n M_n$ behaves like $(\lambda_n^\alpha\sum k_n^\alpha)^{1/\alpha}$ for $\alpha<1$, giving $A_n^{(\alpha)}$ as the control parameter; a single exceptionally active molecule can then catalyse an entire self-sustaining network. The paper also shows that the Mossel-Steel criteria based on expected numbers of catalysed reactions per molecule fail in general once catalysis is heterogeneous (Proposition 3).

## Sources

- J. Kim, E. Sönmez, "Can a self-sustaining chemical network emerge due to just a few catalysts?", arXiv preprint (2026), Theorem 1, Proposition 3, Proposition 6, Theorem 7, Theorem 8, Proposition 9, <https://doi.org/10.48550/arXiv.2611.06033>.
