# Optimal affinity for deliverable capacity

For a Langmuir–Freundlich isotherm with exponent $\eta$, the deliverable capacity between two positive pressures is largest when $b = (p_{\max}p_{\min})^{-\eta/2}$.

Let $n(p) = n_m\,b\,p^{\eta}/(1 + b\,p^{\eta})$ with $n_m > 0$ and $\eta > 0$ fixed, and pressures
$0 < p_{\min} < p_{\max}$. As a function of the affinity $b > 0$ alone the deliverable capacity
$k(b) = n(p_{\max}) - n(p_{\min})$ has the unique maximizer $b^\ast = (p_{\max}p_{\min})^{-\eta/2}$, and

$$
k(b^\ast) = n_m\,\frac{(p_{\max}/p_{\min})^{\eta/2} - 1}{(p_{\max}/p_{\min})^{\eta/2} + 1}.
$$

Scaling both pressures by $\lambda > 0$ leaves the maximal value unchanged but multiplies $b^\ast$ by
$\lambda^{-\eta}$. If $b = b(T)$ depends on temperature over an admissible set with $n_m$ and $\eta$ fixed, then the
temperatures with $b(T) = b^\ast$, if any, are exactly those where the deliverable capacity equals $k(b^\ast)$; when no
admissible temperature has $b(T) = b^\ast$, every attained capacity is strictly below $k(b^\ast)$, a maximizing temperature
need not exist, and the supremum of the attained capacities can still equal $k(b^\ast)$. At $p_{\min} = 0$ the value
$n_m$ is only a supremum, approached as $b \to \infty$.

## Context

Research level. The model of Bhatia and Myers underlies an optimal H2 adsorption enthalpy of about 15–20 kJ/mol quoted by Zhang et al.; Murray, Dincă and Long report 13.6 kJ/mol for 298 K between 1.5 and 100 bar from the Langmuir analysis, and 22–25 kJ/mol for 298 K between 1.5 and 30 bar after an entropy–enthalpy correction — targets pursued with open-metal-site frameworks.

## Depends on

- [Deliverable adsorption capacity](deliverable-adsorption-capacity.md)
- [Langmuir–Freundlich isotherm](langmuir-freundlich-isotherm.md)

## Proof depends on

None.

## Expansion

With $A = p_{\max}^{\eta}$, $B = p_{\min}^{\eta}$, $k(u) = n_mu(A-B)/((1+uA)(1+uB))$, whose derivative has the sign
of $1 - u^2AB$; $k(0^+) = k(\infty) = 0$ and $k > 0$ in between, so $u = (AB)^{-1/2}$ is the unique maximizer, and
$k = n_m(A-B)/(\sqrt A + \sqrt B)^2 = n_m(\sqrt A - \sqrt B)/(\sqrt A + \sqrt B)$ there. The temperature statement
follows by composing with $b(T)$: $k(b(T)) \le k(b^\ast)$ with equality exactly when $b(T) = b^\ast$ (for example
$b(T) = Tb^\ast$ on $0 < T < 1$ never attains $b^\ast$, yet its capacities approach $k(b^\ast)$ as $T \to 1$).

## Sources

- L. Zhang, M. D. Allendorf, R. Balderas-Xicohténcatl, D. P. Broom, G. S. Fanourgakis, G. E. Froudakis, T. Gennett, K. E. Hurst, S. Ling, C. Milanese, P. A. Parilla, D. Pontiroli, M. Riccò, S. Shulda, V. Stavila, T. A. Steriotis, C. J. Webb, M. Witman and M. Hirscher, "Fundamentals of hydrogen storage in nanoporous materials", *Progress in Energy* 4, 042013 (2022), [doi.org](https://doi.org/10.1088/2516-1083/ac8d44), section 3.1.2, Eqn (9) and the attribution of the optimum to Bhatia and Myers.
- L. J. Murray, M. Dincă and J. R. Long, "Hydrogen storage in metal–organic frameworks", *Chemical Society Reviews* 38, 1294–1314 (2009), [doi.org](https://doi.org/10.1039/b802256a), section "Design principles for an optimal H2 adsorbent" ($\Delta H_{opt}$ from Langmuir isotherms).
