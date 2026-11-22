# Bounded mean oscillation

A locally integrable $f \colon \mathbb{R} \to \mathbb{R}$ has bounded mean oscillation (is in $\mathrm{BMO}$) when

$$\|f\|_{\mathrm{BMO}} = \sup_I \frac{1}{|I|} \int_I |f - f_I| < \infty, \qquad f_I = \frac{1}{|I|} \int_I f,$$

the supremum running over bounded intervals (A. K. Lerner, *A "local mean oscillation" decomposition and some its applications*, lecture notes (https://u.math.biu.ac.il/~lernera/paseky.pdf), §2.1, with $n = 1$; the space was introduced by F. John and L. Nirenberg in 1961). Bounded functions and $\log|x|$ are in $\mathrm{BMO}$. The two central results are stated with the BMO condition written out explicitly:

- the [John–Nirenberg inequality](exists-volume-abs-sub-average-gt-le.md): the distribution of $|f - f_I|$ on $I$ decays exponentially, at a rate set by $\|f\|_{\mathrm{BMO}}$; its classical proof iterates the [dyadic Calderón–Zygmund decomposition](../dyadic-maximal-function/calderon-zygmund.md) of $(f - f_I) \mathbf{1}_I$ at height $2\|f\|_{\mathrm{BMO}}$;
- [Fefferman's $H^1$–$\mathrm{BMO}$ inequality](exists-enorm-integral-mul-le-poisson-max.md): $\mathrm{BMO}$ pairs boundedly with the Hardy space $H^1$, the inclusion $\mathrm{BMO} \subseteq (H^1)^*$ of C. Fefferman's duality theorem $(H^1)^* = \mathrm{BMO}$.

- [John–Nirenberg inequality](exists-volume-abs-sub-average-gt-le.md)
- [Fefferman's $H^1$–$\mathrm{BMO}$ inequality](exists-enorm-integral-mul-le-poisson-max.md)
