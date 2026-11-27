# Weak chimeras without symmetry in weakly coupled oscillator populations

**Setting.** For a smooth $2\pi$-periodic coupling function $g$ with $g(0) = 0$, the fully symmetric network of $n$ phase oscillators is $\dot\varphi_k = Y_k(\varphi) = \frac1n\sum_{j=1}^n g(\varphi_k - \varphi_j)$ on $\mathbb{T}^n$, which is $S_n$-equivariant and leaves the canonical region $\mathcal{C} = \{0 = \varphi_1 < \varphi_2 < \dots < \varphi_n < 2\pi\}$ invariant (after removing the phase-shift symmetry). Two such populations $\varphi^1, \varphi^2 \in \mathbb{T}^n$ are weakly coupled,

$$\dot\varphi^{\ell}_k = Y_k(\varphi^{\ell}) + \frac{\varepsilon}{n}\sum_{j=1}^n g\big(\varphi^{\ell}_k - \varphi^{3-\ell}_j\big),\qquad \ell = 1,2,$$

a system with symmetry group $S_n \wr S_2$. For a compact invariant $A \subseteq \mathcal{C}$ let $\Xi(A) = \bigcup_{k \ne j}\{\varphi_k - \varphi_j : \varphi \in A\}$; sets $A_1, A_2$ are *coupling function separated* if $\Xi(A_\ell) \subseteq Q_\ell$ for open intervals $Q_1, Q_2 \subseteq \mathbb{T}$ with disjoint closures. A set is *sufficiently stable* if it has a neighbourhood carrying a Lyapunov function.

**Theorem.** Suppose that, for the uncoupled dynamics with coupling function $g$, $A_{\mathrm{coh}} \subseteq \mathcal{C}$ is a sufficiently stable relative equilibrium (or, more generally, a compact sufficiently stable attractor) and $A_{\mathrm{inc}} \subseteq \mathcal{C}$ is a sufficiently stable attractor, the two are coupling function separated, and both have trivial setwise symmetry, $\Sigma(A_{\mathrm{coh}}) = \Sigma(A_{\mathrm{inc}}) = \{\mathrm{id}\}$. Then for every sufficiently small $\delta > 0$ there exist a smooth coupling function $\hat g$ and $\varepsilon_0 > 0$ such that for all $0 \le \varepsilon < \varepsilon_0$ the coupled system with $\hat g$ has a [weak chimera](weak-chimeras-as-partial-isotropy-of-the-angular-frequency-vector.md) $A(\varepsilon) \subseteq B_\delta(A_{\mathrm{coh}} \times A_{\mathrm{inc}})$ with $\Sigma(A(\varepsilon)) = \{\mathrm{id}\}$.

## Expansion

Because the two invariant sets only use phase differences in disjoint intervals, $g$ can be modified away from $\Xi(A_1)\cup\Xi(A_2)$ to a $\hat g$ that keeps both sets invariant but pushes the ranges of possible average frequencies on them apart by a margin larger than the perturbation size. Persistence of sufficiently stable invariant sets under the weak coupling then gives $A(\varepsilon)$ near the product. Inside $\mathcal{C}^2$ the cyclic order within each population is preserved, so all oscillators of one population share a frequency (nontrivial isotropy), while the separated frequency ranges keep the two populations' frequencies different (isotropy not all of $\Gamma$). Trivial symmetry of the factors passes to the product attractor and to nearby invariant sets, so the frequency synchrony here is not explained by any symmetry of the solution; an explicit $C^\infty$ coupling function gives a chaotic weak chimera of this kind.

## Depends on

- [Weak chimeras as partial isotropy of the angular frequency vector](weak-chimeras-as-partial-isotropy-of-the-angular-frequency-vector.md)

## Sources

- Bick C, "Isotropy of Angular Frequencies and Weak Chimeras with Broken Symmetry", J Nonlinear Sci (2017), Section 5, Eqs. (21)–(24) and (29), Definition 4, Lemmas 1 and 3, Theorems 2–3, Remark 4, <https://doi.org/10.1007/s00332-016-9345-2>, PMCID PMC5367817.
