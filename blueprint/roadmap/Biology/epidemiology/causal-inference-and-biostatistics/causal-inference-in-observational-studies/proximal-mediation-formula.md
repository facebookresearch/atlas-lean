# Proximal mediation formula for the natural direct and indirect effects

**Setting.** Observed data are $(X, Z, A, M, W, Y)$: baseline covariates $X$, a binary exposure $A \in \{0,1\}$, a mediator $M$
with support $\mathcal S$, an outcome $Y$, and two proxies $Z$ (exposure-inducing) and $W$ (outcome-inducing) of an unmeasured
confounder $U$. Write $M(a)$ and $Y(a,m)$ for potential outcomes. The target is the cross-world mean $\psi = E[Y\{1, M(0)\}]$,
from which the natural direct effect $E[Y\{1,M(0)\}] - E[Y\{0,M(0)\}]$ and the natural indirect effect
$E[Y\{1,M(1)\}] - E[Y\{1,M(0)\}]$ follow.

**Assumptions.**
1. *Consistency:* $M(a) = M$ when $A = a$, and $Y(a,m) = Y$ when $A = a, M = m$.
2. *Positivity:* $f_{M\mid A,U,X}(m \mid A,U,X) > 0$ for all $m \in \mathcal S$, and $0 < \Pr(A = 1 \mid U, X) < 1$, almost surely.
3. *Latent exchangeability:* $Y(a,m) \perp A \mid U,X$; $Y(a,m) \perp M(a) \mid A = a, U, X$; $M(a) \perp A \mid U, X$.
4. *Latent cross-world independence:* $Y(a,m) \perp M(a^*) \mid U, X$ for all $a, a^*$ and $m$.
5. *Proxies:* $Z \perp M(a) \mid A,U,X$; $Z \perp Y(a,m) \mid A, M(a), U, X$; $W \perp (A, Z) \mid M(a), U, X$; $W \perp M(a) \mid U, X$.
6. *Completeness:* if $E\{g(U) \mid Z, A=1, M, X\} = 0$ a.s. then $g(U) = 0$ a.s.; and if $E\{g(U) \mid Z, A=0, X\} = 0$ a.s. then
   $g(U) = 0$ a.s., for square-integrable $g$.

**Theorem.** Suppose there are *outcome confounding bridge functions* $h_1(w, m, x)$ and $h_0(w, x)$ solving the integral equations

$$E(Y \mid Z, A=1, M, X) = \int h_1(w, M, X)\, dF(w \mid Z, A=1, M, X),$$

$$E\{h_1(W, M, X) \mid Z, A=0, X\} = \int h_0(w, X)\, dF(w \mid Z, A=0, X).$$

Then under Assumptions 1–6 the same equations hold with $Z$ replaced by $U$, and

$$\psi = E[Y\{1, M(0)\}] = \iint h_0(w, x)\, dF(w \mid x)\, dF(x).$$

## Expansion

Completeness lets one pass from the observable equations conditional on $Z$ to the latent equations conditional on $U$: their
difference is a function of $U$ whose conditional mean given $Z$ vanishes. Conditional on $(U, X)$ the classical assumptions of
Pearl's mediation formula hold, and $h_1$ plays the role of $E(Y\mid U, A=1, M, X)$ integrated against the mediator law under
$A = 0$, which the nested bridge $h_0$ encodes; averaging $h_0(W,X)$ over $(W, X)$ then averages over $U$. When $U$ is empty the
formula reduces to Pearl's mediation formula $\iint E(Y\mid A=1,m,x)\,dF(m\mid A=0,x)\,dF(x)$. (Dukes, Shpitser and Tchetgen
Tchetgen 2023, published edition: Assumptions 1–6, Theorem 1 and Equations 2–6.)

## Sources

- O. Dukes, I. Shpitser, and E. J. Tchetgen Tchetgen, "Proximal mediation analysis", Biometrika (2023), <https://doi.org/10.1093/biomet/asad015>; accepted version in the journal's format <https://par.nsf.gov/servlets/purl/10428415>. Numbering of the published edition: Assumptions 1–6, Theorem 1 and Equations 2–6. The arXiv preprint (2109.11904) numbers these differently.
