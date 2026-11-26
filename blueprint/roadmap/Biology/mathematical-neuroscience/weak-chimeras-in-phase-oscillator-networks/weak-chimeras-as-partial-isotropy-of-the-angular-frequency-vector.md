# Weak chimeras as partial isotropy of the angular frequency vector

**Setting.** Let $\Gamma \subseteq S_n$ act transitively on $\mathbb{C}_\bullet^n = (\mathbb{C}\setminus\{0\})^n$ by permuting coordinates, and let $F:\mathbb{C}_\bullet^n \to \mathbb{C}^n$ be $\Gamma$-equivariant, defining the oscillator system $\dot z_k = z_k F_k(z)$, $k = 1,\dots,n$, with well-defined dynamics on $\mathbb{C}_\bullet^n$. The asymptotic angular frequency of oscillator $k$ along the trajectory from $z_0$ is

$$\Omega_k(z_0) = \lim_{T\to\infty}\frac{1}{T}\int_0^T \operatorname{Im}F_k(z(t))\,dt,$$

the average change of $\arg z_k$ per unit time, and $\Omega(z_0) = (\Omega_1(z_0),\dots,\Omega_n(z_0))$ is the *angular frequency vector*. For phase oscillators $\dot\varphi = Y(\varphi)$ on $\mathbb{T}^n$ (embedded by $z_k = e^{i\varphi_k}$) this is $\Omega_k(\varphi_0) = \lim_{T\to\infty}\hat\varphi_k(T)/T$ for a continuous lift $\hat\varphi$. The limits exist for all quasi-regular initial conditions, a set of full measure for every invariant measure. Write $\Gamma_{\Omega(z_0)} = \{\gamma \in \Gamma : \gamma\Omega(z_0) = \Omega(z_0)\}$ for the isotropy subgroup.

**Definition.** A compact, connected, chain-recurrent, dynamically invariant set $A \subseteq \mathbb{C}_\bullet^n$ is a *weak chimera* if

$$\{\mathrm{id}\} \subsetneq \Gamma_{\Omega(z_0)} \subsetneq \Gamma\qquad\text{for all } z_0 \in A.$$

**Properties.**

1. For an invariant set $A$ with instantaneous symmetry group $T(A)$ and setwise symmetry group $\Sigma(A)$, carrying an ergodic invariant measure,

$$\{\mathrm{id}\} \subseteq T(A) \subseteq \Sigma(A) \subseteq \Gamma_{\Omega(A)} \subseteq \Gamma,$$

so any nontrivial symmetry of a solution forces some frequency synchrony.
2. If $A$ is a weak chimera then so is $\gamma A$ for every $\gamma \in \Gamma$.
3. If along a solution the winding of one coordinate stays bounded while another winds at a positive linear rate, then $\Gamma_{\Omega} \ne \Gamma$; this covers amplitude-mediated and pure amplitude chimeras.

## Expansion

The map $\operatorname{Im}F$ is a $\Gamma$-equivariant observable, and $\Omega$ is its time average, so a symmetry of the set carries time averages to time averages and fixes $\Omega$, giving property 1; equivariance of $F$ gives property 2. Compared with the original definition, which asks only that some permutation in $S_n$ fix $\Omega$, this version counts only oscillators related by a symmetry of the system, so it is invariant under the system's symmetries; for a ring with only cyclic symmetry the two definitions can differ. The converse of property 1 fails: frequency synchrony can arise without any symmetry of the solution.

## Sources

- Bick C, "Isotropy of Angular Frequencies and Weak Chimeras with Broken Symmetry", J Nonlinear Sci (2017), Section 3, Eqs. (11)–(15), Definitions 2–3, Propositions 2–3; Theorem 1 (quasi-regular points), <https://doi.org/10.1007/s00332-016-9345-2>, PMCID PMC5367817.
