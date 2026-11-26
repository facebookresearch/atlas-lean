# Global existence for the elastic-cortex model of adhesion-independent migration

**Model.** A cell confined between two plates is represented by its actin cortex, a closed curve $X(\cdot,t) : \mathbb{T} \to \mathbb{R}^2$ parametrized by the amount of actin $s \in \mathbb{T} = [0,1)$, whose total is normalized to $1$. The cortex resists stretching but not compression, the cytoplasm has a constant excess pressure $p>0$, and the channel $\Omega_c$ is softened by an obstacle potential $W_\delta = (\delta + \rho_\delta * \mathbf{1}_{\Omega_c})^{-1}$. These give the energy

$$E_\delta(X) = \int_{\mathbb{T}}\Big(\tfrac12(|\partial_s X| - 1)_+^2 + \tfrac{p}{2}X\cdot\partial_s X^\perp + W_\delta(X)\Big)\,ds,$$

whose pressure term equals $-p|\Omega(t)|$. Net polymerization at rate $g(s,t)$ per actin unit, with $\int_{\mathbb{T}} g\,ds = 0$ so that total cortical actin is conserved, drives a cortical flow with material derivative $D/Dt = \partial_t + \big(\int_0^s g\,d\sigma\big)\partial_s$. A compensating force from the intracellular back-transport of actin removes the net motion of a free cell. Combining both into a flow operator $S_{\rm flow}$, friction with the surrounding fluid gives the degenerate parabolic system

$$\partial_t X + \partial_s\big(S_{\rm flow}[X]\big) = \partial_s\Big((|\partial_s X|-1)_+\frac{\partial_s X}{|\partial_s X|}\Big) - p\,\partial_s X^\perp - \nabla W_\delta(X), \qquad X(\cdot,0) = X^0 .$$

**Assumptions.** (A1) $p < 2\pi$. (A2) $\|S_{\rm flow}[X]\|_{L^2} \le c\|X\|_{L^2}$ and $\|\partial_s S_{\rm flow}[X]\|_{L^2} \le c\|X\|_{H^1}$. (A3) $\Omega_c$ has smooth boundary and $x\cdot\nabla W_\delta(x) \ge 0$ for small $\delta$, which roughly means $\Omega_c$ is star-shaped about the origin. (A4) $X^0 \in H^1(\mathbb{T})^2$ with $X^0(\mathbb{T}) \subset \Omega_c$.

**Theorem.**

1. *(Coercivity)* If $p < 2\pi$, then $E_\delta(X) \ge \tfrac12\big(1 - \tfrac{p}{2\pi}\big)\|\partial_s X\|_2^2 - \|\partial_s X\|_2 \ge -\pi/(2\pi - p)$.
2. *(Penalized problem)* Under (A1)–(A4) and for $\delta$ small, there is a global solution $X_\delta \in H^1_{\rm loc}(\mathbb{R}_+; L^2) \cap L^\infty_{\rm loc}(\mathbb{R}_+; H^1)$, with bounds uniform in $\delta$. It is Hölder continuous with exponent $\tfrac12$ in $s$ and $\tfrac14$ in $t$.
3. *(Hard walls)* Along a subsequence $\delta\to 0$, $X_\delta$ converges uniformly on bounded time intervals to a limit $X$ in the same spaces. The limit satisfies $X \in \overline{\Omega_c}$ and solves the equation without $\nabla W_\delta$ wherever $X(s,t) \in \Omega_c$.

Without flow and obstacles, the equilibrium is the circle $X_{\rm equ}(s) = (2\pi - p)^{-1}(\cos 2\pi s, \sin 2\pi s)$, which exists only when $p < 2\pi$.

## Expansion

The elastic term is the $L^2$-gradient of a convex functional, while the pressure and obstacle terms are continuous perturbations. The cortical flow is non-variational, so it is treated explicitly in a semi-implicit minimizing-movement scheme. Each time step minimizes $E_\delta$ plus a quadratic distance and a linear flow term. Coercivity, which rests on the isoperimetric inequality $|\Omega| \le L^2/(4\pi)$, gives discrete energy bounds that are uniform in the step and in $\delta$. A modified Morrey inequality then gives equicontinuity, which allows passage to the continuum and the hard-wall limit. Simulations with front polymerization and rear depolymerization reproduce leukocyte migration in microchannels without adhesion.

## Sources

- G. Jankowiak, D. Peurichard, A. Reversat, C. Schmeiser and M. Sixt, "Modelling adhesion-independent cell migration", arXiv:1903.09426 (2019), Section 3 (model), assumptions (A1)–(A4), Theorems 1–2, Remark 1 and Lemma 1, <https://doi.org/10.48550/arXiv.1903.09426>.
