# Structural sign test for steady-state sensitivities of chemical reaction networks

**Setting.** Consider a chemical reaction network with $n_s$ species and $n_r$ reactions. Let $\alpha_{jk}\ge0$ be the reactant stoichiometry of species $j$ in reaction $k$, let $A=(\alpha_{jk})$, and let $\Gamma\in\mathbb R^{n_s\times n_r}$ be the stoichiometry matrix. The dynamics are $\dot x=f(x)=\Gamma R(x)$ on the positive orthant. The kinetics satisfy the reactant-monotonicity axiom: for every $x>0$,

$$\frac{\partial R_k}{\partial x_j}(x)>0\iff\alpha_{jk}>0,\qquad \frac{\partial R_k}{\partial x_j}(x)=0\iff\alpha_{jk}=0 .$$

Mass-action kinetics satisfy it. Steady states may also obey constraints $g(x)=0$, such as conservation laws, whose Jacobian $g'$ has entries of constant sign. Let $x(\lambda)$ be a smooth curve of steady states with $f(x(\lambda))=0$ and $g(x(\lambda))=0$, for instance obtained by varying a total enzyme concentration. The **sensitivity** is $S(\lambda)=dx/d\lambda$, and the question is to determine $\pi=\operatorname{sign}S(\lambda)\in\{-1,0,1\}^{n_s}$ independently of $\lambda$ and of the kinetic constants.

**Key lemma.** Let $\Sigma(x)=\{\operatorname{sign}(vR'(x)):v\in\operatorname{rowspan}\Gamma\}\cup\{\operatorname{sign}(e_i^\top g'(x))\}$. Then $S(\lambda)\in\mathcal N(f'(x(\lambda)))\cap\mathcal N(g'(x(\lambda)))$. Hence for every $\sigma\in\Sigma(x(\lambda))$ the sign vector $\pi=\operatorname{sign}S(\lambda)$ satisfies

$$\mathrm{XNOR}\big(\exists i:\sigma_i\pi_i>0,\ \exists j:\sigma_j\pi_j<0\big).$$

In words, either $\sigma_i\pi_i=0$ for all $i$, or there are indices of both signs.

**Theorem (state-independent constraints).**

1. For any $x>0$, any nonnegative row vector $\rho$ and any species $j$: $\rho A_j=0\iff\rho\,\partial_jR(x)=0$ and $\rho A_j>0\iff\rho\,\partial_jR(x)>0$. Here $A_j$ is row $j$ of $A$ written as a column.
2. Let $\mathcal V_G$ be the set of $v=\nu\Gamma$ such that, for every species $j$, either $v^+A_j=0$ or $v^-A_j=0$, where $v^\pm$ are the positive and negative parts of $v$. For such $v$, $\operatorname{sign}(vR'(x))=\operatorname{sign}(vA^\top)$ for every $x>0$. Hence $\Sigma_0':=\{\operatorname{sign}(vA^\top):v\in\mathcal V_G\}\subseteq\Sigma(x)$ for all states.
3. *(Purely combinatorial version.)* Let $\bar\alpha=\operatorname{sign}A^\top\in\{0,1\}^{n_r\times n_s}$. Let $\mathcal S_G$ be the set of sign vectors $s$ of the row space of $\Gamma$ such that, for each $j$, $s^+\bar\alpha_j=0$ or $s^-\bar\alpha_j=0$. Then $s=\operatorname{sign}v\in\mathcal S_G$ iff $v\in\mathcal V_G$, in which case $\operatorname{sign}(vA^\top)=\operatorname{sign}(s\bar\alpha)$. So

$$\Sigma_0=\{\operatorname{sign}(s\bar\alpha):s\in\mathcal S_G\}\subseteq\bigcap_\lambda\Sigma(x(\lambda))$$

is computable from the network's sign patterns alone.

**Consequence.** Every feasible sensitivity sign $\pi$ must satisfy the conjunction $\bigwedge_{\sigma\in\Sigma_0\cup\operatorname{sign}g'}\mathrm{XNOR}(p_{\sigma,\pi},q_{\sigma,\pi})$. Sieving the $3^{n_s}$ candidate sign vectors leaves the possible sign patterns of the steady-state response. This uses only linear algebra and logic, with no simulation and no knowledge of rate constants, and in many examples it leaves a unique or nearly unique sign pattern, up to the trivial pair $\pm\pi$.

## Expansion

The key lemma is immediate. If $vS=0$ with $\operatorname{sign}v=\sigma$, the terms $v_iS_i$ cannot all be of one strict sign, so a positive term forces a negative term. The difficulty is that $\Sigma(x)$ depends on the unknown state through $R'(x)$. The trick is to use vectors $v$ in the row space of $\Gamma$ whose positive and negative parts never share a reactant species. For such $v$, $v\,\partial_jR(x)$ is either $v^+\partial_jR(x)\ge0$ or $-v^-\partial_jR(x)\le0$. By item 1 its sign is read off from $A$, uniformly in $x$. Item 3 replaces real vectors by their signs, using $\operatorname{sign}(uw)=\operatorname{sign}(\operatorname{sign}u\cdot\operatorname{sign}w)$ for one-signed $u,w$. Enumerating the sign vectors of a subspace is an oriented-matroid covector computation. Testing the conjunction for a given $\pi$ is a satisfiability-type problem, NP-hard in general, but exhaustive search is fast for moderate $n_s$.

These are the main logical lemma (Section 2) and the sign lemmas, proposition and corollary of Section 4 of the source.

## Sources

- E. D. Sontag, "A technique for determining the signs of sensitivities of steady states in chemical reaction networks", arXiv:1312.7538 (2013). <https://doi.org/10.48550/arXiv.1312.7538>
