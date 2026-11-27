# Protein structural alignment as low order value optimization

**Setting.** Let proteins $A$ and $B$ be given by the coordinates of their $C_\alpha$ atoms, and let $x \in \mathbb{R}^n$ parametrize a rigid-body displacement (rotation and translation) of $B$. For each admissible correspondence $i \in \{1, \dots, m\}$ between atoms of $A$ and atoms of $B$ (a finite set), let $f_i(x)$ be a smooth score of that correspondence at displacement $x$. The STRUCTAL score of a correspondence is

$$\mathrm{STRUCTAL} = \sum_{\text{aligned pairs}} \frac{20}{1 + (d/2.24)^2} - 10\, n_g,$$

where $d$ is the distance between corresponding $C_\alpha$ atoms and $n_g$ the number of gaps.

**Low order value optimization (LOVO).** Structural alignment is the problem of maximizing

$$f(x) = \max\{f_1(x), \dots, f_m(x)\},$$

the best score over all correspondences, as a function of the displacement. Equivalently (after negation) one minimizes $f_{\min}(x) = \min_i f_i(x)$, with active set $I_{\min}(x) = \{ i : f_i(x) = f_{\min}(x)\}$. A point $x^*$ is **critical** if $\nabla f_i(x^*) = 0$ for some $i \in I_{\min}(x^*)$; such points are Clarke stationary.

**Two-step scheme.** A convergent method alternates (A) choosing a correspondence in the active set for the current displacement and (B) a step that strictly improves the score of that fixed correspondence. Dynamic programming over monotone bijections yields the best bijective correspondence for a given orientation (DP-LS); the non-bijective correspondence that maps each atom of the smaller protein to its nearest atom of the other globally maximizes any score that increases as distances decrease (NB-LS). In both, step (B) is a safeguarded line-search Newton iteration on $f_\nu$ rather than the RMSD-minimizing Procrustes superposition used by STRUCTAL, which optimizes a different objective and can oscillate between alignments.

## Proof depends on

- [Armijo sufficient decrease condition](../../../../Analysis/numerical-analysis/line-search-methods/armijo-condition.md)

## Expansion

Since the set of correspondences is finite, the objective is the upper envelope of finitely many smooth functions; it is non-smooth only where two correspondences tie. The LOVO framework shows that one may ignore this non-smoothness and take the gradient of any active function: a sufficient increase of the active $f_\nu$ at fixed correspondence implies an increase of the envelope, because re-optimizing the correspondence at the new point can only increase the score further. Hence the score is monotone across iterations, which the classical alternation with Procrustes does not guarantee.

## Sources

- L. Martínez, R. Andreani, J. M. Martínez, "Convergent algorithms for protein structural alignment", BMC Bioinformatics 8 (2007) 306, Results (LOVO interpretation, DP-LS and NB-LS algorithms) and Methods (Algorithm A1, Theorems 1 and 2), <https://doi.org/10.1186/1471-2105-8-306> (PMC1995224).
