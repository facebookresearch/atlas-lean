# Feinberg's decomposition theorem for positive steady states

Let $\mathcal N$ be a chemical reaction network with species $X_1,\dots,X_m$ and reaction set $\mathcal R$, with kinetics $K$ assigning a rate function $K_r:\mathbb R^m_{>0}\to\mathbb R_{\ge 0}$ to each reaction $r:y_r\to y_r'$, so that

$$\dot x=f(x)=\sum_{r\in\mathcal R}K_r(x)\,(y_r'-y_r).$$

A partition $\mathcal R=\mathcal R_1\sqcup\dots\sqcup\mathcal R_\alpha$ induces subnetworks $\mathcal N_i$ with kinetics $K_i=K|_{\mathcal R_i}$, species-formation rates $f_i(x)=\sum_{r\in\mathcal R_i}K_r(x)(y_r'-y_r)$, and stoichiometric subspaces $S_i=\operatorname{span}\{y_r'-y_r:r\in\mathcal R_i\}$. The decomposition is **independent** if the stoichiometric subspace $S$ of $\mathcal N$ is the direct sum $S=S_1\oplus\dots\oplus S_\alpha$, equivalently $\operatorname{rank}S=\sum_i\operatorname{rank}S_i$. Let $E$ and $E_i$ denote the sets of positive steady states of $\mathcal N$ and $\mathcal N_i$.

**Theorem (Feinberg).** For every decomposition, $E_1\cap\dots\cap E_\alpha\subseteq E$. If the decomposition is independent, then

$$E_1\cap E_2\cap\dots\cap E_\alpha=E .$$

## Expansion

Since $f=f_1+\dots+f_\alpha$, a common zero of all $f_i$ is a zero of $f$, which is the inclusion. If the decomposition is independent and $f(x)=0$, then $0=\sum_i f_i(x)$ with $f_i(x)\in S_i$, and the directness of the sum forces $f_i(x)=0$ for each $i$. The result holds for any kinetics, mass-action or power-law, provided each reaction keeps its rate function in its subnetwork. The paper uses it to derive analytic steady-state parametrizations: compute the finest independent decomposition, solve each small subnetwork (for instance via deficiency-zero, weakly reversible translations whose complex-balanced equilibria have monomial parametrizations), and intersect. In the two-species example $R_1:\emptyset\to A$, $R_2:\emptyset\to B$, $R_3:A+B\to B$, $R_4:B\to\emptyset$ with mass action, the partition $\{R_1,R_3\},\{R_2,R_4\}$ has ranks $1+1=2$, and the unique positive steady state is $(a,b)=(k_1k_4/(k_2k_3),\,k_2/k_4)$.

## Sources

- B. S. Hernandez, P. V. N. Lubenia, M. D. Johnston, J. K. Kim, "A framework for deriving analytic steady states of biochemical reaction networks", PLOS Computational Biology 19(4) (2023) e1011039, <https://doi.org/10.1371/journal.pcbi.1011039>, PMCID PMC10129002. Section "Network decomposition" and Theorem 1 (after M. Feinberg, Lectures on chemical reaction networks, and M. Feinberg, *Foundations of chemical reaction network theory*, Springer, 2019).
