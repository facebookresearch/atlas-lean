# Two identical molecular motors can be slower than one

**Model.** A cargo is towed along a microtubule by processive motors (kinesin or dynein), each tethered to the cargo by a linear spring. In the regime where motors stay attached and the cargo relaxes fast compared with motor stepping (the in vitro regime analyzed by asymptotics), each attached motor moves at velocity $g(f)$, a function of the force $f$ it bears normalized by its stall force, and the cargo feels a constant external force $F$ (normalized). The nondimensional *stallibility* $s$ is the ratio of a typical spring force to the stall force. With two motors separated by a distance $r$, the springs load the leading and trailing motors with forces $s(F\pm r)/2$, and the effective cargo velocity $v_2(F)$ is the average of $\tfrac12\bigl(g(s(F+r)/2)+g(s(F-r)/2)\bigr)$ over the stationary distribution of the separation $r$; a single motor has $v_1(F)=g(sF)$.

**Assumption on the force–velocity curve.** $g$ is smooth, bounded with bounded derivatives, $g(0)=1$, $g(1)=0$, strictly decreasing, concave on $(-\infty,f_*]$ and convex on $[1-f_*,\infty)$ for some $f_*\in(0,\tfrac12)$, and *strongly concave*: $g(f)+g(-f)$ decreases and $g(1+f)+g(1-f)$ increases in $f>0$. Physically, an assisting force speeds a motor up only slightly while an equal hindering force slows it a lot.

**Theorem.**

1. *(Two motors can be slower than one.)* For every $s$ there is $F_c(s)>0$ such that $v_2(F)<v_1(F)$ for all $F<F_c(s)$, in particular at zero load.
2. *(Superadditive stall force.)* If $s<1$, the stall forces $F_j^*=\min\{F:v_j(F)\le0\}$ satisfy

$$F_2^*>2F_1^* .$$

3. *(Including cargo fluctuations.)* When the thermal fluctuations of the cargo position are kept (the source's Section 5.3), write $\mathcal{A}_g(m,\sigma^2)$ for the average of $g$ against the normal law with mean $m$ and variance $\sigma^2$. Then a single motor has velocity $\mathcal{A}_g(sF, s^2/2)$. With two motors at positions $x=(x_1,x_2)$ and load $F$, motor $i$ has the cargo-averaged drift $\bar g_i(x;F)=\int_{\mathbb R}g\big(s(x_i-z)\big)\,\pi_Z(z;x,F)\,dz$, where $\pi_Z(\cdot\,;x,F)$ is the Gaussian stationary density of the cargo position given the motor positions and the load (the source's (9)–(10), with $F$ its $\tilde\theta$), and $v_2(F)$ is the average of $\tfrac12\big(\bar g_1(x;F)+\bar g_2(x;F)\big)$ over the stationary law of the motor configuration under load $F$. At zero load the drift depends only on the signed separation $r$: $\bar g_1(x;0)=\bar g_2(x;0)=G(r):=\mathcal{A}_g(-rs/2, s^2/4)$ (the source's (29)), so $v_2(0)$ is the average of $\tfrac12(G(r)+G(-r))$ over the stationary law of $r$. There are $s_*,\theta_*>0$ such that $v_2(F)<v_1(F)$ for all $s<s_*$ and $|F|<\theta_*$; the key estimate is $\tfrac12(G(r)+G(-r))<G(0)$ for all $r>0$, which gives the case $F=0$, and continuity in $F$ extends it to $|F|<\theta_*$.

Thus the common mean-field assumption that bound motors share the load equally overestimates the speed of multi-motor cargo at low load and underestimates its stall force.

## Expansion

At zero external load the two springs exert equal and opposite forces $\pm sr/2$ on the motors, so the cargo velocity is $\tfrac12(g(sr/2)+g(-sr/2))$, which by strong concavity is strictly below $g(0)=1$ for every $r\ne0$; averaging over the nondegenerate stationary law of $r$ gives $v_2(0)<v_1(0)$, and continuity extends this to small $F$. Near stall the convexity of $g$ above $1-f_*$ reverses the inequality: unequal loading lets the less-loaded motor keep pulling, so the pair resists more than twice the single-motor stall force. The effective velocity and diffusivity come from a homogenization (law of large numbers plus central limit theorem) of the slow motor positions driven by the fast cargo fluctuations, $M(t)\approx v_2t+\sqrt{2D_2t}\,Z$.

## Sources

- Scott A. McKinley, Avanti Athreya, John Fricks, Peter R. Kramer, "Asymptotic analysis of microtubule-based transport by multiple identical molecular motors", Journal of Theoretical Biology 305 (2012), 54–69, <https://doi.org/10.1016/j.jtbi.2012.03.035>. Published version of arXiv:1111.0684, cited next; locators there refer to the arXiv version.
- S. A. McKinley, A. Athreya, J. Fricks, P. R. Kramer, "Asymptotic Analysis of Microtubule-Based Transport by Multiple Identical Molecular Motors", arXiv:1111.0684 (2011), Assumption 1, Section 5 (Propositions 5.1–5.2, Lemma 5.3, Theorem 5.4) and the effective drift–diffusion limit preceding them. <https://doi.org/10.48550/arXiv.1111.0684>
