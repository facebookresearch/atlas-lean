# Two-locus quasi-linkage equilibrium approximation

Work in the setting of the [uniform weak-selection bound on two-locus linkage disequilibrium](two-locus-ld-contraction-under-weak-selection.md): gametes $AB,Ab,aB,ab$ with frequency vector $x$ on the probability simplex, the [diploid viability-selection and meiosis map](two-locus-viability-selection-with-recombination.md) with symmetric viabilities $w_{ij}=1+\varepsilon a_{ij}$, $|a_{ij}|\le1$, $a_{14}=a_{23}$, $0\le\varepsilon\le\frac12$, and recombination fraction $r\in[0,\frac12]$ with $r\ge r_0>0$. The fitness array $(a_{ij})$ and $r$ do not depend on time (autonomous fitnesses). Write $D=x_1x_4-x_2x_3$ and $p=(p_A,p_B)$ with $p_A=x_1+x_2$, $p_B=x_1+x_3$, $p_a=1-p_A$, $p_b=1-p_B$. Every simplex state is $x=\hat x(p)+D\,e$ with $\hat x(p)=(p_Ap_B,\,p_Ap_b,\,p_ap_B,\,p_ap_b)$ and $e=(1,-1,-1,1)$, where $D$ ranges over the feasible interval

$$I(p)=\bigl[\max(-p_Ap_B,\,-p_ap_b),\ \min(p_Ap_b,\,p_ap_B)\bigr].$$

**(a) Neutral case $\varepsilon=0$ (exact).** The map is $x_i'=x_i-e_irD$, so allele frequencies are constant and $D_{t+1}=(1-r)D_t$. Hence $D_t=(1-r)^tD_0\to0$ geometrically. No finite-time bound of order $\varepsilon^2$ is asserted at $\varepsilon=0$: for $r=\frac14$ and $x_{AB}=x_{ab}=\frac12$ one has $D_t=\frac14(\frac34)^t>0$ for every $t$.

**(b) Positive case $0<\varepsilon\le\varepsilon_0$.** For a frozen allele-frequency vector $p$ let $\Phi_{p,\varepsilon}(D)$ be the linkage disequilibrium of the image of $\hat x(p)+De$ under one generation of the map, for $D\in I(p)$. There are constants $\varepsilon_0,K,K',K''>0$ depending only on $r_0$ such that, for every $p$ and every permitted fitness array:

1. $|\Phi_{p,\varepsilon}(D)-\Phi_{p,\varepsilon}(D')|\le(1-r_0)(1+K\varepsilon)\,|D-D'|$ for $D,D'\in I(p)$, and $\Phi_{p,\varepsilon}$ has a unique fixed point $D^*(p,\varepsilon)\in I(p)$;
2. $|D^*(p,\varepsilon)|\le K\varepsilon/r_0$;
3. for every initial state and every $t\ge T(\varepsilon)=\lceil K'\log(1/\varepsilon)/r_0\rceil$,

    $$|D_t-D^*(p_t,\varepsilon)|\le K''\varepsilon^2 .$$

Part (b) is the two-locus form of Nagylaki's quasi-linkage-equilibrium regime: after a time of order $\log(1/\varepsilon)$ generations, linkage disequilibrium is of order $\varepsilon$ and tracks a slowly varying quasi-equilibrium value with error of order $\varepsilon^2$.

## Depends on

- [A uniform weak-selection bound on two-locus linkage disequilibrium](two-locus-ld-contraction-under-weak-selection.md)
- [Diploid two-locus viability selection followed by meiosis](two-locus-viability-selection-with-recombination.md)

## Expansion

A full proof page must establish the following.

- Part (a) from the neutral recombination identity, including the displayed counterexample $D_0=\frac14$, $D_t=\frac14(\frac34)^t$, which shows that part (a) and not the order-$\varepsilon^2$ bound governs $\varepsilon=0$.
- The decomposition $x=\hat x(p)+De$ and the feasible interval $I(p)$ (nonnegativity of the four coordinates).
- The Lipschitz bound in (b)1: write $\Phi_{p,\varepsilon}(D)=(1-r)D+\varepsilon\psi_{p,\varepsilon}(D)$ with $\psi$ Lipschitz in $D$ uniformly in $p$ and in the fitness array, and use $1-r\le1-r_0$.
- That $\Phi_{p,\varepsilon}$ maps $I(p)$ into itself, or a replacement for this step. The image of $\hat x(p)+De$ has allele frequencies $p'\ne p$ in general, so the image disequilibrium lies a priori in $I(p')$, not $I(p)$; near the boundary of the simplex $I(p)$ is short. A complete proof either proves self-mapping of $I(p)$ or defines $D^*(p,\varepsilon)$ as the fixed point of the polynomial extension of $\Phi_{p,\varepsilon}$ to a fixed neighbourhood and then shows that it is feasible. This is an open obligation of the page.
- The bound (b)2 from the uniform estimate $|\Phi_{p,\varepsilon}(0)|\le C\varepsilon$ and the contraction constant.
- The tracking bound (b)3: first the uniform bound of the dependency page gives $|D_t|=O(\varepsilon/r_0)$ after $O(\log(1/\varepsilon)/r_0)$ generations; then compare $D_{t+1}=\Phi_{p_t,\varepsilon}(D_t)+O(\varepsilon^2)$ (allele frequencies move by $O(\varepsilon)$ per generation and $D^*$ is Lipschitz in $p$ with constant $O(\varepsilon)$) with the fixed point, and iterate the contraction for a further $O(\log(1/\varepsilon)/r_0)$ generations.

## Sources

- T. Nagylaki, *The evolution of multilocus systems under weak selection*, Genetics 134 (1993), 627–647, <https://pmc.ncbi.nlm.nih.gov/articles/PMC1205503/> (statement and proof; the abstract distinguishes the $O(s)$ disequilibrium regime after time $t_1\sim(\ln s)/\ln(1-c_{\min})$ and the $O(s^2)$ quasi-equilibrium regime after $t_2\sim2t_1$).
