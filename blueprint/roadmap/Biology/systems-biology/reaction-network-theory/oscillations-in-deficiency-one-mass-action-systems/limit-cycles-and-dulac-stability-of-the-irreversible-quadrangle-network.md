# Limit cycles and Dulac stability of the irreversible quadrangle network

**Setting.** A planar mass-action system has two species $X, Y$, complexes $(a_i, b_i) \in \mathbb{R}^2$ (meaning $a_i X + b_i Y$), reactions $(i,j)$ with rate constants $\kappa_{ij} > 0$, and dynamics

$$\dot x = \sum_{(i,j)} (a_j - a_i)\,\kappa_{ij}\,x^{a_i}y^{b_i}, \qquad \dot y = \sum_{(i,j)} (b_j - b_i)\,\kappa_{ij}\,x^{a_i}y^{b_i}$$

on $\mathbb{R}^2_+$, with reaction vectors spanning $\mathbb{R}^2$. The **deficiency** is $\delta = m - \ell - s$ (complexes minus linkage classes minus rank). For $\delta = 0$ there are no positive periodic orbits and, under weak reversibility, the positive equilibrium is globally stable.

The **irreversible quadrangle** is the cycle $(a_1,b_1) \to (a_2,b_2) \to (a_3,b_3) \to (a_4,b_4) \to (a_1,b_1)$ through four distinct, non-collinear complexes; it is weakly reversible with $\delta = 4 - 1 - 2 = 1$.

**Theorem.**
1. For all rate constants the quadrangle system is permanent and has a unique positive equilibrium, at which the Jacobian has positive determinant. Hence the equilibrium is asymptotically stable when the trace is negative, repelling when the trace is positive (and then, by permanence and Poincaré–Bendixson, a stable limit cycle exists), and a center-focus when the trace vanishes.
2. Rate constants can produce oscillations: for complexes $(0,1), (1,0), (1,2), (0,3)$ the equilibrium is repelling and surrounded by a stable limit cycle for suitable $\kappa$; for $(0,1), (0,0), (1,2), (1,5)$ there are rate constants with at least three limit cycles.
3. (Global stability.) Let $a_i = \min_k a_k$ and $b_j = \min_k b_k$ (indices mod 4). If neither $a_i < a_{i+3} < a_{i+1} < a_{i+2}$ nor $b_j < b_{j+3} < b_{j+1} < b_{j+2}$ holds, there is no periodic orbit and the unique positive equilibrium is globally asymptotically stable for every choice of rate constants.

## Expansion

The deficiency-one theorem gives uniqueness and nondegeneracy of the equilibrium; permanence of weakly reversible planar systems and the index $+1$ of the equilibrium force the determinant to be positive, so only the trace decides local stability. Three limit cycles arise by rescaling the equilibrium to $(1,1)$, tuning one parameter to make the trace vanish, and computing focal (Lyapunov) values: where the first focal value $L_1$ changes sign with $L_2 > 0$, successive perturbations create two small cycles inside the large stable cycle guaranteed by permanence. For item 3, the Dulac function $h = x^{-\alpha}y^{-\beta}$ gives

$$\frac{\operatorname{div}(hf, hg)}{h} = \sum_{i=1}^4 (\alpha - a_i)(a_i - a_{i+1})\kappa_i x^{a_i - 1}y^{b_i} + \sum_{i=1}^4 (\beta - b_i)(b_i - b_{i+1})\kappa_i x^{a_i}y^{b_i - 1},$$

and the ordering conditions are exactly those under which $\alpha, \beta$ can be chosen to make every coefficient nonpositive and some negative. Irreversible chains of three reactions and three separate reactions, which have deficiency one but fall outside the deficiency-one theorem, can likewise have centers (via reversibility $\dot x = f(x,y)$, $\dot y = -f(y,x)$), homoclinic loops, and up to four limit cycles.

## Depends on

- [Weakly reversible reaction network](../../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)

## Proof depends on

- [Poincaré–Bendixson theorem](../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Sources

- B. Boros, J. Hofbauer, "Oscillations in planar deficiency-one mass-action systems", Journal of Dynamics and Differential Equations (2024), Section 2 (Definitions 1–4, Theorems 1–3), Section 3 (quadrangle: Sections 3.1–3.3, Proposition 1) and Sections 4–5 (Propositions 4–7), <https://doi.org/10.1007/s10884-021-10051-z>, PMCID PMC10901957.
