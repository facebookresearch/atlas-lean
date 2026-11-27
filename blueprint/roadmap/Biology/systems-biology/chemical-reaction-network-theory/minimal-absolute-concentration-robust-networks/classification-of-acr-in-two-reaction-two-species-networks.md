# Classification of absolute concentration robustness in two-reaction, two-species networks

**Setting.** A mass-action system $\dot x = f(x)$ on $\mathbb{R}^n_{\ge 0}$ has **static ACR** in species $x_i$ if it has a positive steady state and all positive steady states lie in one hyperplane $\{x_i = a_i^*\}$; it has **dynamic ACR** if, in addition, $x_i(t) \to a_i^*$ for every positive initial condition whose stoichiometric compatibility class meets that hyperplane (*weak* dynamic ACR asks only for convergence to the hyperplane set-wise). A dynamic ACR species is **full basin** if every positive initial condition is compatible with the hyperplane and **wide basin** if the incompatible values of $x_i$ are bounded above. A network has the *capacity* for a property if it holds for some rate constants.

Consider networks with species $X, Y$ and two reactions

$$a_1X + b_1Y \xrightarrow{k_1} \tilde a_1X + \tilde b_1Y, \qquad a_2X + b_2Y \xrightarrow{k_2} \tilde a_2X + \tilde b_2Y,$$

with nonnegative real coefficients, $(\tilde a_i,\tilde b_i) \ne (a_i,b_i)$, reaction vectors $v_i = (\tilde a_i - a_i,\ \tilde b_i - b_i)$ and stoichiometric subspace $\mathcal{S} = \operatorname{span}\{v_1,v_2\}$.

**Theorem (one reaction or one species).** A network with only one reaction is never static or dynamic ACR. A one-species network is static ACR (for all rate constants) if and only if it has a unique positive steady state for every choice of rate constants, and is dynamic ACR if and only if that unique steady state is moreover globally attracting for every choice.

**Theorem (static ACR).** For the two-reaction networks above, the capacity for static ACR, static ACR and strong static ACR are equivalent, and hold if and only if

1. the source complexes differ, $(a_1,b_1) \ne (a_2,b_2)$;
2. they share a coordinate, $(a_2 - a_1)(b_2 - b_1) = 0$;
3. the reaction vectors point in opposite directions, $v_1 = -\mu v_2$ for some $\mu > 0$ (so $\dim\mathcal{S} = 1$).

Then exactly one species is ACR: $X$ if $a_1 \ne a_2$, with value $x^* = (k_2/(\mu k_1))^{1/(a_1-a_2)}$, and $Y$ if $b_1 \ne b_2$, with value $y^* = (k_2/(\mu k_1))^{1/(b_1-b_2)}$.

**Theorem (dynamic ACR when $\dim\mathcal{S} = 1$).** The capacity for weak dynamic ACR, weak dynamic ACR, full-basin weak dynamic ACR, the capacity for dynamic ACR and full-space dynamic ACR are all equivalent to: the network is static ACR and

$$(\tilde a_1 - a_1)(a_2 - a_1) + (\tilde b_1 - b_1)(b_2 - b_1) > 0,$$

i.e. the reaction arrows point toward each other's source. The dynamic ACR species and value coincide with the static ones. The dynamic ACR species is wide basin if and only if $(\tilde a_1 - a_1)(\tilde b_1 - b_1) \le 0$, and full basin if and only if $(\tilde a_1 - a_1)(\tilde b_1 - b_1) = 0$.

**Theorem (invariant hyperplane, general $\dim\mathcal{S}$).** The network has a unique invariant line $\{x=x^*\}$ with $x^*>0$ if and only if $b_1=b_2$, $a_1\ne a_2$ and $(\tilde a_1-a_1)(\tilde a_2-a_2)<0$; symmetrically, it has a unique invariant line $\{y=y^*\}$ with $y^*>0$ if and only if $a_1=a_2$, $b_1\ne b_2$ and $(\tilde b_1-b_1)(\tilde b_2-b_2)<0$ (Theorem 4.1(1)). The source's summary Theorem 5.1(1) prints this as "a unique invariant hyperplane parallel to a coordinate axis exists if and only if the reactant polytope is parallel to the other axis"; this page states the condition of Theorem 4.1(1) instead, because the printed form fails in the "if" direction: $X\to2X$, $2X\to3X$ has sources on a segment parallel to the $x$-axis but $\dot x=k_1x+k_2x^2>0$, so no line $\{x=x^*\}$ is invariant. For such networks every ACR property holds for all rate constants as soon as it holds for one; the hyperplane is weakly attracting if and only if both reactions point inward, $(\tilde a_i - a_i)(a_j - a_i) + (\tilde b_i - b_i)(b_j - b_i) > 0$ for $i \ne j$; and, with the convention $0\cdot(1/0) = 0$, the network is subspace dynamic ACR if and only if

$$\sum_{i\ne j\in\{1,2\}}\left[(a_j - a_i)\frac{\tilde b_i - b_i}{\tilde a_i - a_i} + (b_j - b_i)\frac{\tilde a_i - a_i}{\tilde b_i - b_i}\right] \ge 0,$$

cylinder dynamic ACR if the sum is strictly positive (when neither $\dot x$ nor $\dot y$ vanishes identically), and full basin dynamic ACR if each summand is nonnegative. The ACR value of $x$ (when $a_1 \ne a_2$) is $\left(-k_2(\tilde a_2 - a_2)/(k_1(\tilde a_1 - a_1))\right)^{1/(a_1-a_2)}$.

## Expansion

With two reactions, $f(x,y) = k_1x^{a_1}y^{b_1}v_1 + k_2x^{a_2}y^{b_2}v_2$. A positive steady state needs the two terms to cancel, which forces $v_1 = -\mu v_2$; then $f = \big(k_2x^{a_2}y^{b_2} - \mu k_1x^{a_1}y^{b_1}\big)v_2$ vanishes exactly on the curve $x^{a_1-a_2}y^{b_1-b_2} = k_2/(\mu k_1)$, which is a coordinate hyperplane precisely when one exponent difference is zero, giving the static classification and the ACR value. Dynamically, every trajectory stays on the line through its initial point in direction $v_2$ and moves along it with the sign of the scalar prefactor; it approaches the steady-state hyperplane exactly when the arrows point toward each other's sources, which is the inner-product condition. The basin type depends on whether the line in direction $v_1$ through every positive point meets the hyperplane inside the positive orthant, a sign condition on the components of $v_1$. When the reaction vectors are independent, the hyperplane can still be invariant and attracting, and the summed slope conditions decide from which regions trajectories reach it.

## Sources

- Badal Joshi and Gheorghe Craciun, "Reaction network motifs for static and dynamic absolute concentration robustness", arXiv:2201.08428 (2022), Theorems 3.2–3.7 and 4.1–4.3, and the summary Theorem 5.1, <https://doi.org/10.48550/arXiv.2201.08428>. Published version: SIAM Journal on Applied Dynamical Systems 22 (2023) 501–526, <https://doi.org/10.1137/22m1476162>.
