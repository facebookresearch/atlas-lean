# Quasi-linkage-equilibrium approximation of two-locus clines

**Model.** Two diallelic loci $\mathcal A$, $\mathcal B$ with allele frequencies $p_A,p_B$ and linkage disequilibrium $D$ evolve on $\mathbb{R}$ under diffusive migration, additive-across-loci selection with dominance $h_A,h_B$, and recombination:

$$
\begin{aligned}
\dot p_A&=p_A''+\lambda\alpha(x)p_A(1-p_A)\vartheta_A+\lambda\beta(x)\vartheta_BD,\\
\dot p_B&=p_B''+\lambda\beta(x)p_B(1-p_B)\vartheta_B+\lambda\alpha(x)\vartheta_AD,\\
\dot D&=D''+2p_A'p_B'+\lambda\bigl[\alpha(x)(1-2p_A)\vartheta_A+\beta(x)(1-2p_B)\vartheta_B\bigr]D-\rho D,
\end{aligned}
$$

with $\vartheta_A=1+h_A-2h_Ap_A$, $\vartheta_B=1+h_B-2h_Bp_B$, step environments $\alpha(x)=\alpha_+$, $\beta(x)=\beta_+$ for $x\ge0$ and $\alpha(x)=-\alpha_-$, $\beta(x)=-\beta_-$ for $x<0$ (all $\alpha_\pm,\beta_\pm>0$), selection intensity $\lambda$ and scaled recombination rate $\rho$. A two-locus cline is a non-constant stationary solution. Solutions scale as $\pi(x,t;c\lambda,c\rho)=\pi(\sqrt c\,x,ct;\lambda,\rho)$.

Let $P,Q$ be the single-locus clines at $\mathcal A$ and $\mathcal B$, $a_\pm=\sqrt{\lambda\alpha_\pm}$, $b_\pm=\sqrt{\lambda\beta_\pm}$, $a_0=P(0)$, and

$$
I_+(x)=\int_x^\infty P'(y)^2Q'(y)\bigl[1+h_B-2h_BQ(y)\bigr]dy,\qquad I_-(x)=\int_{-\infty}^xP'(y)^2Q'(y)\bigl[1+h_B-2h_BQ(y)\bigr]dy .
$$

**Theorem.** Let $\varepsilon=1/\rho$ and assume that for all sufficiently small $\varepsilon>0$ there is a two-locus cline of the form $p_A=P+\varepsilon p+O(\varepsilon^2)$, $p_B=Q+\varepsilon q+O(\varepsilon^2)$, $D=\varepsilon d+O(\varepsilon^2)$, uniformly with first and second derivatives. Then

1. $d(x)=2P'(x)Q'(x)$;
2. $p$ is the unique $C^1$ solution on $\mathbb{R}$ of

$$
p''+\lambda\alpha(x)\bigl[1-2P+h_A(1-6P+6P^2)\bigr]p+2\lambda\beta(x)P'Q'\bigl[1+h_B-2h_BQ\bigr]=0;
$$

3. $p(x)=P'(x)k_\pm(x)$ for $x\gtrless0$, where $k_+(x)=k_0+2b_+^2\int_0^xI_+(y)P'(y)^{-2}dy$, $k_-(x)=k_0-2b_-^2\int_x^0I_-(y)P'(y)^{-2}dy$, and

$$
k_0=\frac{2\sqrt3\,[b_+^2I_+(0)-b_-^2I_-(0)]}{a_0(1-a_0)(1+h_A-2h_Aa_0)\,a_+a_-\sqrt{a_+^2+a_-^2}} .
$$

**Corollary.** The slope correction at the step is

$$
p'(0)=\frac{2\sqrt3\,[a_-^2b_+^2I_+(0)+a_+^2b_-^2I_-(0)]}{a_+a_-\sqrt{a_+^2+a_-^2}}>0,
$$

so the allele-frequency cline becomes steeper at its centre as linkage tightens; in contrast to the single-locus slope, $p'(0)$ depends on dominance. The sign of $p(0)$ can be positive, negative or zero, and $p(x,c\lambda)=c\,p(\sqrt c\,x,\lambda)$.

## Depends on

- [Single-locus cline with dominance in a step environment](single-locus-cline-with-dominance-in-a-step-environment.md)

## Expansion

For loose linkage, recombination rapidly destroys disequilibrium, so to first order $D$ is slaved to the allele frequencies: balancing $\rho D$ against the migration source term $2p_A'p_B'$ (the Wahlund-type association created by mixing populations with different frequencies) gives $d=2P'Q'$. Substituting into the equation for $p_A$ and expanding in $\varepsilon$ yields a linear inhomogeneous equation for $p$ whose homogeneous solution is $P'$ (the derivative of the single-locus cline), so variation of constants gives $p=P'k$, with $k_0$ fixed by $C^1$ matching at the step. Because $I_\pm>0$, the indirect selection transmitted through disequilibrium always adds positive slope at $x=0$, which is the quasi-linkage-equilibrium explanation for why linked loci reinforce each other's clines.

## Sources

- Reinhard Bürger, "Two-locus clines on the real line with a step environment", *Theor. Popul. Biol.* 117 (2017), 1-22. <https://doi.org/10.1016/j.tpb.2017.08.002>
- Preprint version (the locators in this item follow its numbering): Reinhard Bürger, *Two-locus clines on the real line with a step environment*, arXiv (2017). Lemma 2.3 (invariance), Theorem 4.1 (first-order approximation), Corollary 4.3 (properties of $p$), Section 4. <https://doi.org/10.48550/arXiv.1708.03499>
