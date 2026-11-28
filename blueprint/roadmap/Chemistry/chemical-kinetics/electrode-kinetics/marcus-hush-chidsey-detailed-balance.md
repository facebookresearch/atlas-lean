# Detailed balance and reciprocity of Marcus–Hush–Chidsey rates

The Marcus–Hush–Chidsey rates satisfy the de Donder relation $k_{\mathrm{red}}(\eta)/k_{\mathrm{ox}}(\eta)=e^{-e\eta/k_BT}$ and the reciprocity $k_{\mathrm{ox}}(-\eta)=k_{\mathrm{red}}(\eta)$, so $k_{\mathrm{ox}}(\eta)=e^{e\eta/k_BT}k_{\mathrm{ox}}(-\eta)$.

For the [Marcus–Hush–Chidsey rates](marcus-hush-chidsey-rate.md) with $A,\lambda,k_BT>0$ and every real $\eta$: both rates are
strictly positive (their integrands are positive continuous functions and $A>0$), and

$$\frac{k_{\mathrm{red}}(\eta)}{k_{\mathrm{ox}}(\eta)}=\exp\!\Big(-\frac{e\eta}{k_BT}\Big),\qquad k_{\mathrm{ox}}(-\eta)=k_{\mathrm{red}}(\eta),\qquad
\frac{k_{\mathrm{ox}}(\eta)}{k_{\mathrm{ox}}(-\eta)}=\exp\!\Big(\frac{e\eta}{k_BT}\Big).$$

In particular $k_{\mathrm{red}}(0)=k_{\mathrm{ox}}(0)$, the exchange rate, and the net reduction rate
$k_{\mathrm{red}}-k_{\mathrm{ox}}$ is negative exactly for $\eta>0$.

## Context

Research-level electrode kinetics. The de Donder relation is the thermodynamic consistency condition for a one-electron reaction; the [Butler–Volmer law](butler-volmer-equation.md) with $n=1$ satisfies it only for complementary transfer coefficients $\alpha_a+\alpha_c=1$, whereas Marcus–Hush–Chidsey kinetics satisfies it identically.

## Depends on

- [Marcus–Hush–Chidsey rate at a metal electrode](marcus-hush-chidsey-rate.md)

## Proof depends on

None.

## Expansion

Reciprocity is the substitution $\eta\mapsto-\eta$ in the definitions. For de Donder, substitute $x\mapsto-x$ (Lebesgue measure is reflection invariant) in $k_{\mathrm{red}}$ and use $1/(1+e^{-u})=e^u/(1+e^u)$; with $u=x/k_BT$ and $(x+\lambda+e\eta)^2-(x-\lambda+e\eta)^2=4\lambda(x+e\eta)$ the integrand becomes $e^{-e\eta/k_BT}$ times that of $k_{\mathrm{ox}}$. Zeng et al. state both relations (Sec. II and Eq. (10)).

## Sources

- Y. Zeng, R. Smith, P. Bai and M. Z. Bazant, Simple formula for Marcus–Hush–Chidsey kinetics, *Journal of Electroanalytical Chemistry* 735 (2014), 77–83; numbers from arXiv:1407.5370v1, Sec. II, Eqs. (1)–(2) (Butler–Volmer with $\alpha$ and $1-\alpha$; de Donder relation) and the reciprocity relation after Eq. (4); Sec. IV, Eq. (10). [arXiv:1407.5370v1](https://arxiv.org/abs/1407.5370v1); [doi:10.1016/j.jelechem.2014.09.038](https://doi.org/10.1016/j.jelechem.2014.09.038)
