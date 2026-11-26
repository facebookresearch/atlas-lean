# Rao potential diversity under a capacity constraint

**Setting.** A community of $S$ species at a location has composition $p\in\Delta_{S-1}=\{p\ge0,\ \sum_sp_s=1\}$. For a symmetric dissimilarity matrix $A=(a_{st})$ (trait, phylogenetic or functional distances, $a_{ss}=0$), Rao's quadratic entropy is $Q_A(p)=p^\top Ap$, the expected dissimilarity of two individuals drawn independently. Local capacity is encoded by species-specific latent intensities $\Lambda_s>0$ and a capacity level $c$, giving the feasible set

$$\mathcal C=\{p\in\Delta_{S-1}:\ \Lambda^\top p=c\}.$$

Given an observed composition $p^{\rm obs}\in\mathcal C$, the *Rao potential diversity* and *diversity gap* are

$$V_A=\max_{p\in\mathcal C}p^\top Ap,\qquad G_A=V_A-(p^{\rm obs})^\top Ap^{\rm obs}.$$

Let $\mathcal T=\{v:\mathbf 1^\top v=\Lambda^\top v=0\}$ be the tangent space of $\mathcal C$.

**Theorem (existence, uniqueness, stability).** Assume $\mathcal C\neq\emptyset$.

1. $V_A$ is attained and $G_A\ge0$.
2. If $v^\top Av\le0$ on $\mathcal T$, then $Q_A$ is concave on $\mathcal C$; if the inequality is strict for $v\ne0$, the maximizer is unique.
3. For any other symmetric $\widetilde A$ with the same $\mathcal C$ and $p^{\rm obs}$, $|V_A-V_{\widetilde A}|\le\|A-\widetilde A\|_{\max}$ and $|G_A-G_{\widetilde A}|\le2\|A-\widetilde A\|_{\max}$, with no concavity assumption and constants independent of $S$.
4. If $-v^\top Av\ge\kappa\|v\|_2^2$ on $\mathcal T$ for some $\kappa>0$, the maximizer $p_A^*$ is unique and every maximizer for $\widetilde A$ satisfies $\|p_A^*-p_{\widetilde A}^*\|_2\le\|A-\widetilde A\|_{\rm op}/\kappa$.

**Theorem (entropic selection).** Let $\mathcal C\subseteq\Delta_{S-1}$ be nonempty, compact and convex, $A$ conditionally negative semidefinite on $\mathcal C-\mathcal C$, and $r$ a reference composition with all $r_s>0$. Let $p^\dagger$ minimize $D_{\rm KL}(p\|r)$ over the maximizers of $Q_A$ on $\mathcal C$; it is unique. For $\tau>0$ the regularized maximizer $p_\tau(A)=\arg\max_{p\in\mathcal C}\{Q_A(p)-\tau D_{\rm KL}(p\|r)\}$ is unique,

$$0\le V_A-Q_A(p_\tau(A))\le\tau D_{\rm KL}(p^\dagger\|r)\le\tau\log\frac1{\min_sr_s},$$

$p_\tau(A)\to p^\dagger$ as $\tau\downarrow0$, and $\|p_\tau(A)-p_\tau(\widetilde A)\|_2\le\frac2\tau\|A-\widetilde A\|_{\rm op}$ for any $\widetilde A$ satisfying the same concavity condition.

## Expansion

Attainment is compactness of $\mathcal C$; $G_A\ge0$ because $p^{\rm obs}$ is feasible. Concavity of a quadratic on an affine slice depends only on its curvature along the slice. The value bounds follow from $|p^\top(A-\widetilde A)p|\le\|A-\widetilde A\|_{\max}$ for any probability vector, which is why they need neither uniqueness nor curvature; the composition bound is the usual strong-concavity argument comparing first-order optimality conditions. For squared Euclidean trait distances $a_{st}=\|z_s-z_t\|^2$, $A$ is conditionally negative semidefinite, so the maximizer can be non-unique; the KL penalty toward a reference composition selects one benchmark continuously, with an explicit bias of order $\tau$. The gap $G_A$ maps how far a site's observed functional diversity lies below the maximum its capacity allows.

## Sources

- Shinto Eguchi, "An information-geometric framework for mapping maximum potential biodiversity", arXiv:2606.09906 (2026), Theorems 5.1 and 5.2 (Section 5); capacity projection and Pythagorean identity in Propositions 4.1-4.2, <https://doi.org/10.48550/arXiv.2606.09906>
