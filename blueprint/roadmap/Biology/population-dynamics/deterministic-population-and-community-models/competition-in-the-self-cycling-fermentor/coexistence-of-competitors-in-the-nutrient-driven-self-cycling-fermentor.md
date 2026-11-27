# Coexistence of competitors in the nutrient-driven self-cycling fermentor

**Model.** In a self-cycling fermentor, $n$ microbial populations $x_j$ consume one limiting nutrient $s$. Between decanting events,

$$\dot s = -\sum_{j=1}^n x_j f_j(s), \qquad \dot x_j = x_j\bigl(f_j(s) - d_j\bigr), \qquad s(t) \ne \bar s,$$

and whenever the nutrient falls to the trigger level $\bar s$ a fraction $r \in (0,1)$ of the medium is replaced by fresh medium at concentration $s^{\mathrm{in}} > \bar s > 0$:

$$s(t^+) = r s^{\mathrm{in}} + (1-r)\, s(t^-), \qquad x_j(t^+) = (1-r)\, x_j(t^-), \qquad s(t^-) = \bar s.$$

Yields are scaled to $1$; $d_j \ge 0$ are decay rates; each $f_j$ is $C^1$, non-decreasing, with $f_j(0) = 0$ (e.g. Monod $f_j(s) = m_j s/(K_j + s)$). Let $\bar s^+ = r s^{\mathrm{in}} + (1-r)\bar s$ and $\mu_j = \int_{\bar s}^{\bar s^+} \bigl(1 - d_j/f_j(s)\bigr)\,ds$, the net growth of species $j$ over one cycle when alone, and assume the technical condition $\mu_{\min} > 0$ (it implies every $\mu_j > 0$). Start from $s(0) = \bar s^+$.

**Single species.** If only species $\ell$ is present and $\mu_\ell > 0$, there is a unique nontrivial periodic orbit, with one impulse per period, which is globally asymptotically stable; at impulses $x_\ell(t_k^-) = \mu_\ell / r$ and $x_\ell(t_k^+) = (1-r)\mu_\ell / r$.

**Exclusion.** If $f_j(s) - d_j > f_k(s) - d_k$ for all $s \in (\bar s, \bar s^+)$, then $x_k \to 0$.

**Persistence.** For $n = 2$ each single-species orbit has Floquet multipliers $1$, $1-r$ and a third one $\Lambda_{jk}$ (orbit of species $j$, invader $k$). If $|\Lambda_{12}| > 1$ and $|\Lambda_{21}| > 1$, every solution with $x_1(0), x_2(0) > 0$ is persistent: $\liminf_{t\to\infty} x_1(t) > 0$ and $\liminf_{t\to\infty} x_2(t) > 0$.

**No decay: complete classification.** If $d_1 = d_2 = 0$, then $s + x_1 + x_2 \to s^{\mathrm{in}}$, and on that invariant set exactly one of the following holds: there is a periodic orbit with both species present and one impulse per period; all solutions converge to the species-1 orbit; or all converge to the species-2 orbit. Hence, when both $|\Lambda_{jk}| > 1$, all solutions with both species present converge to a positive periodic orbit with one impulse per period. For Monod responses,

$$\Lambda_{jk} = \left(\frac{1}{1-r}\right)^{\frac{m_k(K_j + s^{\mathrm{in}})}{m_j(K_k + s^{\mathrm{in}})} - 1} \left(\frac{K_k + \bar s^+}{K_k + \bar s}\right)^{\frac{m_k(K_j - K_k)}{m_j(K_k + s^{\mathrm{in}})}}, \qquad j \ne k,$$

so coexistence requires the two response curves to cross between $\bar s$ and $\bar s^+$, unlike the chemostat, where competitive exclusion holds.

## Proof sketch

Each cycle runs the nutrient from $\bar s^+$ down to $\bar s$ and the total amount of nutrient-plus-biomass is reset by the same factor at every impulse, which is why $s + \sum x_j$ relaxes to $s^{\mathrm{in}}$ when there is no decay and the two-species system reduces to a planar impulsive system on a strip. Mutual invadability is computed by impulsive Floquet theory: the nontrivial multiplier of the species-$j$ orbit in the direction of $x_k$ is $(1-r)$ times the exponential of the growth of $k$ over one period, and changing variables from time to nutrient level turns that integral into $\int_{\bar s}^{\bar s^+} f_k/(f_j (s^{\mathrm{in}} - s))\, ds$, which is explicit for Monod kinetics. Persistence then follows from uniform persistence arguments once both boundary orbits are unstable, and the trichotomy from analysing the one-dimensional return map on the impulse section.

## Sources

- Stacey R. Smith, Tyler Meadows and Gail S.K. Wolkowicz, "Competition in the nutrient-driven self-cycling fermentation process", *Nonlinear Analysis: Hybrid Systems* 54 (2024), 101519, <https://doi.org/10.1016/j.nahs.2024.101519>. Preprint version: arXiv:2405.08735 (2024), Propositions 1-3, Theorem 1, Lemma 1, Theorem 2, Corollary 1 and the Monod multiplier computed in the appendix on Floquet multipliers, <https://doi.org/10.48550/arXiv.2405.08735>.
