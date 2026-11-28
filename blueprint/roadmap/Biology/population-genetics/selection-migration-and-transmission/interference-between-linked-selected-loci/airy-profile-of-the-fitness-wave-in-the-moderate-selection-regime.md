# Airy profile of the fitness wave in the moderate-selection regime

In the [traveling-wave framework](traveling-wave-self-consistency-for-fixation-probabilities.md) with mutation spectrum $\mu(s)$, speed $v$ and coalescent timescale $T_c$ defined by $v = \int \mu(s)\,s\,e^{T_c s}\,ds$, define the fitness scales

$$b^3 = \tfrac{1}{2}\int \mu(s)\, s^2 e^{T_c s}\,ds, \qquad c = T_c v - \int \mu(s)\bigl(e^{T_c s} - 1\bigr)\,ds,$$

and write $f(x) = e^{-T_c x}\psi(x)$, $w(x) = e^{T_c x}\xi(x)$. Taylor expansion of $\psi(x - s)$ and $\xi(x+s)$ to second order (after the exponential prefactors are removed) gives $b^3\psi'' = (c - x)\psi$ and the same equation for $\xi$, so below the nose

$$f(x) \propto e^{-T_c x}\,\mathrm{Ai}\Bigl(\frac{c - x}{b}\Bigr), \qquad w(x) \propto e^{T_c x}\,\mathrm{Ai}\Bigl(\frac{c - x}{b}\Bigr), \qquad N f(x) w(x) \propto \mathrm{Ai}^2\Bigl(\frac{c - x}{b}\Bigr),$$

with nose position $x_c \approx c + |z_0|\,b - 1/T_c$, where $z_0 \approx -2.34$ is the least negative zero of $\mathrm{Ai}$. The approximation is valid when $T_c b \gg 1$ and the relevant effects satisfy $s \ll b$ (more precisely, the maximum typical fixed effect is small compared with the fitness spread $\Delta x_f \sim b$ of future common ancestors). In that regime the fixation probability of a mutation of effect $s$ is

$$p_{\mathrm{fix}}(s) \approx \frac{e^{T_c s}}{N}, \qquad s \ll b,$$

which replaces the independent-site (Kimura) fixation probability and applies to effects of either sign within $s \ll b$, including the intermediate range $T_c |s| \sim 1$ that the infinitesimal and strong-selection limits miss. For a single beneficial effect, $\mu(s) = U\delta(s - s_b)$:

- if $T_c s_b \ll 1$ (infinitesimal regime, valid when $U/s_b \gg \log(N^3 U s_b^2) \gg 1$), $T_c \approx s_b^{-1}\bigl[2 (s_b/U) \log(N^3 U s_b^2)\bigr]^{1/3}$ and $b \approx (U s_b^2/2)^{1/3}$;
- if $T_c s_b \gg 1$, $T_c \approx s_b^{-1} \log\bigl[(s_b/U) \log(NU)\bigr]$.

## Depends on

- [Traveling-wave self-consistency for fixation probabilities](traveling-wave-self-consistency-for-fixation-probabilities.md)

## Expansion

Substituting the exponential ansatz moves the fast factor $e^{\pm T_c s}$ into the mutation kernel, after which the remaining profiles vary on the scale $b$ and second-order Taylor expansion is accurate when $s \ll b$; the definitions of $b$ and $c$ are exactly the coefficients that reduce the equation to Airy form. Matching $w$ and $w'$ to the large-fitness solution $w \approx x$ across a boundary layer fixes $x_c$ (Appendix B of the source). Since $\int f(x) w(x+s)\,dx \propto e^{T_c s}\int \mathrm{Ai}((c-x)/b)\,\mathrm{Ai}((c-x-s)/b)\,dx$ and the integral is insensitive to $s$ when $s \ll b$, normalizing by $p_{\mathrm{fix}}(0) = 1/N$ gives $e^{T_c s}/N$. In the limit $T_c s \to 0$ the expressions reduce to the infinitesimal-model results with $T_c \to \sigma^2/(2D)$, $b \to D^{1/3}$, $c \to \sigma^4/(4D)$.

## Sources

- M. J. Melissa, B. H. Good, D. S. Fisher and M. M. Desai, "Population genetics of polymorphism and divergence in rapidly evolving populations", Genetics 221(4) (2022), iyac053, <https://doi.org/10.1093/genetics/iyac053>, PMCID PMC9339298 (equations (15)–(29), (33)–(40)).
