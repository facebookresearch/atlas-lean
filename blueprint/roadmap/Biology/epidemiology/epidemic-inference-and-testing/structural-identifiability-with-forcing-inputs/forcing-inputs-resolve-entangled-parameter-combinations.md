# Forcing inputs resolve entangled parameter combinations

**Setting.** A model $M(\theta)$ is a rational-function ODE system $\dot x=f(x,u(t),\theta)$, $x(0)=x_0(\theta)$, $y=g(x,\theta)$ with known inputs $u$. Eliminating the states by Ritt's pseudo-division under the standard ranking gives monic *input-output relations* $P(M)$: polynomial differential equations in $y$, $u$ and their derivatives whose coefficients form the *coefficient map* $c(\theta)$. A parameter $\theta_k$ is globally identifiable if $c(\theta)=c(\theta')$ forces $\theta_k=\theta_k'$ (for almost every $\theta$), locally identifiable if this holds within a neighborhood, i.e. the fiber has finitely many values of $\theta_k$; the model is (locally, globally) identifiable if every parameter is. A *forcing input function* $\tilde u$ is a bounded, non-constant, known $C^n$ function of time. *Scaling* a parameter $\tilde\theta$ means replacing $\tilde\theta$ by $\tilde\theta\,\tilde u(t)$ in the state equations; *replacement* means replacing $\tilde\theta$ by $\tilde u(t)$ (scaling with $\tilde\theta$ fixed to $1$).

**Theorem.** Let $M$ be structurally unidentifiable.
1. *Additive combination, scaling (Theorem 2).* Suppose an input-output relation contains, as a multiplicative factor of some coefficient, an identifiable combination $f(\theta_i)+\tilde\theta$ with $f$ rational, while neither $\tilde\theta$ nor $\theta_i$ is identifiable. Scaling $\tilde\theta$ with $\tilde u$ makes $\tilde\theta$ identifiable (locally or globally, as the combination was), and also $\theta_i$ if $f$ is injective. If all other parameters were identifiable, $\tilde M$ is identifiable (Corollary 3).
2. *Two-parameter combination, replacement (Theorem 3).* If $\tilde\theta$ and $\theta_i$ enter only through an identifiable combination $g(\tilde\theta,\theta_i)$ that is injective in $\theta_i$ for fixed $\tilde\theta$ (e.g. $\tilde\theta\theta_i$), replacing $\tilde\theta$ by $\tilde u$ makes $\theta_i$ identifiable (Corollary 4 for the whole model).
3. *Mixed combination, replacement (Theorem 4).* If the coefficient map contains $\theta_j(\tilde\theta+\theta_i)$ with $\theta_i,\theta_j,\tilde\theta$ all unidentifiable, replacing $\tilde\theta$ by a known non-constant $\tilde u$ makes $\theta_i$ and $\theta_j$ globally identifiable (Corollary 5 for the whole model).

**Example.** The two-compartment pharmacokinetic model $\dot x_1=k_{12}x_2-(k_{21}+k_{01})x_1+u_1$, $\dot x_2=k_{21}x_1-(k_{12}+k_{02})x_2$, $y=x_1/V$ has identifiable combinations $\{V,\ k_{12}k_{21},\ k_{02}+k_{12},\ k_{01}+k_{21}\}$ only. Scaling the tissue decay rate $k_{02}$ by a known time-varying proxy $\tilde u(t)$ (part 1 applied to the sum $k_{02}+k_{12}$) makes the whole model structurally identifiable; replacing the blood elimination rate $k_{01}$ by measured data is an instance of part 2.

## Depends on

- [Forcing inputs preserve structural identifiability](forcing-inputs-preserve-structural-identifiability.md)

## Expansion

After scaling, the term $\big(f(\theta_i)+\tilde\theta\big)m$ becomes $f(\theta_i)m+\tilde\theta\,\tilde u\,m$ (times a common factor): the two summands now multiply different known functions of time, so under the solvability assumption their coefficients are identified separately. Replacement removes $\tilde\theta$ from the unknowns altogether, so a combination injective in the remaining parameter pins it down; for $\theta_j(\tilde\theta+\theta_i)=\theta_j\tilde u+\theta_j\theta_i$, the coefficient of the $\tilde u$-term gives $\theta_j$ and then the other gives $\theta_i$. Identifiability of the untouched parameters carries over by the preservation theorem. The practical reading is that a measured time-varying covariate entering through a chosen parameter can break a structural symmetry that no amount of data on the original outputs could break.

## Sources

- Jessica R. Conrad, James M. Hyman, Marisa C. Eisenberg, "Examining the impact of forcing function inputs on structural identifiability", *Mathematical Biosciences* 402 (2026), 109814, Theorems 2-4 and Corollaries 3-5 (Section 5) and the pharmacokinetics example (Sections 3.2 and 8.1), <https://doi.org/10.1016/j.mbs.2026.109814> (preprint arXiv:2407.02771).
