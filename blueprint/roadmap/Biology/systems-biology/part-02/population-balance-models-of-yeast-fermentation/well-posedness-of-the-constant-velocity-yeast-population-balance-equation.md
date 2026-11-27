# Well-posedness of the constant-velocity yeast population balance equation

Let $M=(m_{\min},m_{\max})$, $\Theta=\{m_{\min},m_{\max}\}$, and freeze the substrate concentrations in the yeast population balance model, so that the growth velocity is a constant $\bar r>0$ and the death rate is a constant $\bar k_d=\Phi(E)+k_d\ge0$. The cell-mass density $W(m,t)$ then solves

$$
\partial_tW+\bar r\,\partial_mW+\Sigma(m)W=KW,\qquad W(m_{\min},t)=0,\qquad W(\cdot,0)=W_0,
$$

with $\Sigma(m)=\Gamma(m)+\bar k_d$ and $(KW)(m)=\int_M f(m,m')W(m')\,dm'$, $f(m,m')=p(m,m')\Gamma(m')$, where $\Gamma$ and $p$ are the bounded Gaussian-type division rate and partition kernel of the model.

**Theorem.** Assume $\Sigma\in L^\infty(M)$ with $\Sigma\ge0$, that $f\ge0$ is measurable with $\sup_{m'}\int_Mf(m,m')\,dm<\infty$ and $\sup_m\int_Mf(m,m')\,dm'<\infty$ (so that $K$ is bounded on $L^2(M)$), and $W_0\in L^2(M)$. Let $A=-\bar r\,\partial_m$ with domain $D(A)=\{W\in L^2(M):\partial_mW\in L^2(M),\ W(m_{\min})=0\}$. Then the problem has a unique mild solution $W\in C([0,t_f];L^2(M))$, $W(t)=e^{t(A-\Sigma+K)}W_0$. If in addition $\partial_mW_0\in L^2(M)$ and $W_0(m_{\min})=0$, the solution is strong: $W\in C([0,t_f];D(A))\cap C^1([0,t_f];L^2(M))$. Moreover $W_0\ge0$ implies $W(t)\ge0$ for all $t$.

The source ((2.38b) and Theorem 2.10) imposes $W|_\Theta=0$ at both ends of $M$. At constant speed $\bar r>0$ that overdetermines the transport: $-\bar r\,\partial_m$ with both Dirichlet conditions is not a $C_0$-generator ($\lambda-A$ is not onto, e.g. for the right-hand side $1$), and for $\Sigma=0$, $f=0$ a bump in $W_0$ reaches $m_{\max}$, so no solution exists. The page therefore imposes only the inflow condition at $m_{\min}$.

## Expansion

The advection operator $A$ with the inflow condition generates the nilpotent translation semigroup $(e^{tA}W)(m)=W(m-\bar rt)$ for $m-\bar rt>m_{\min}$ and $0$ otherwise, a positive $C_0$ semigroup on $L^2(M)$. The specific division kernel is bounded by $4\lambda\gamma m_{\max}$ in both integral norms, so $K$ is a bounded positive operator by a Schur-type estimate, and $\Sigma$ is bounded by $\gamma+\bar k_d$. Bounded perturbation theory then shows that $T=A-\Sigma+K$ with $D(T)=D(A)$ generates a positive $C_0$ semigroup, and $W(t)=e^{tT}W_0$ is the solution. Uniqueness follows from the energy identity: for a solution with zero data, $\|W(\tau)\|^2\le 2\|K\|\int_0^\tau\|W(t)\|^2dt$, and Gronwall's lemma gives $W\equiv0$. The general case with mass-dependent growth velocity and substrate coupling is left open.

## Depends on

- [Mass-structured population balance model of yeast in wine fermentation](mass-structured-population-balance-model-of-yeast-in-wine-fermentation.md)

## Proof depends on

- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- C. Schenk, V. H. Schulz, "Existence, Uniqueness and Numerical Modeling of Wine Fermentation Based on Integro-Differential Equations", Section "Existence and Uniqueness of the Solution" ((2.38), Theorem 2.10). <https://doi.org/10.48550/arXiv.2104.06777>
- K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Graduate Texts in Mathematics 194, Springer (2000): the translation semigroups on an interval and their generators (Chapters I–II) and the bounded perturbation theorem (Chapter III, Theorem 1.3), which give the inflow version stated here.
