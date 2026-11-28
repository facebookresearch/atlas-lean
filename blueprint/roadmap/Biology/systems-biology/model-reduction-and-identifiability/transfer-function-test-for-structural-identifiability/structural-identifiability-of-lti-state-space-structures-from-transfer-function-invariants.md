# Structural identifiability of LTI state-space structures from transfer-function invariants

**Structures.** A controlled continuous-time linear time-invariant (LTI) state-space structure $M$ assigns to each parameter $\boldsymbol\theta$ in an open set $\Theta \subseteq \mathbb R^p$ the system

$$\dot{\mathbf x}(t) = \mathbf A(\boldsymbol\theta)\mathbf x(t) + \mathbf B(\boldsymbol\theta)\mathbf u(t), \qquad \mathbf y(t) = \mathbf C(\boldsymbol\theta)\mathbf x(t), \qquad \mathbf x(0) = \mathbf x_0(\boldsymbol\theta),$$

with $\mathbf x \in \mathbb R^n$, $\mathbf u \in \mathbb R^m$, $\mathbf y \in \mathbb R^k$. Positive and compartmental structures restrict states, inputs and outputs to be non-negative and $\mathbf A$ to be a compartmental matrix (non-negative off-diagonal entries, non-positive column sums), as in linear pharmacokinetic and tracer-kinetic models.

**Definition.** For $\boldsymbol\theta \in \Theta$ let $\mathcal I(M) = \{\boldsymbol\theta' \in \Theta : \mathbf y(t,\mathbf u;\boldsymbol\theta') = \mathbf y(t,\mathbf u;\boldsymbol\theta)\ \forall t \in [0,\tau]\}$ for the admissible inputs. If, for almost all $\boldsymbol\theta$, $\mathcal I(M) = \{\boldsymbol\theta\}$, then $M$ is *structurally globally identifiable* (SGI); if $\mathcal I(M)$ is countable, *structurally locally identifiable* (SLI); otherwise *structurally unidentifiable* (SU). The initial state must not be an equilibrium, or the output carries no information on the dynamics.

**Transfer-function test.** By the Laplace transform,

$$\mathcal L\{\mathbf y\}(s;\boldsymbol\theta) = \mathbf V(s;\boldsymbol\theta) + \mathbf W(s;\boldsymbol\theta)\,\mathcal L\{\mathbf u\}(s), \qquad \mathbf V = \mathbf C(s\mathbf I_n - \mathbf A)^{-1}\mathbf x_0, \quad \mathbf W = \mathbf C(s\mathbf I_n - \mathbf A)^{-1}\mathbf B,$$

whose entries are rational functions of $s$ with denominator degree at most $n$ (numerator degree at most $n-1$ for compartmental structures). Writing each entry in canonical form (cancel common factors, make the denominator monic), the coefficients form a vector of invariants $\boldsymbol\phi(\boldsymbol\theta)$: two parameter values give identical outputs for all inputs iff $\boldsymbol\phi(\boldsymbol\theta') = \boldsymbol\phi(\boldsymbol\theta)$. The test is: (1) compute $\boldsymbol\phi(\boldsymbol\theta)$; (2) form $\boldsymbol\phi(\boldsymbol\theta')$; (3) set up $\boldsymbol\phi(\boldsymbol\theta') = \boldsymbol\phi(\boldsymbol\theta)$; (4) solve; (5) classify $M$ as SGI, SLI or SU by the size of the solution set. Including $\mathbf x_0$ in $\mathbf V$ makes known or parameter-dependent initial conditions contribute their own test equations.

**Examples.** For $\dot x = -kx + u$, $y = cx$, $x(0) = 0$: $W(s) = c/(s+k)$, invariants $(c, k)$, so the structure is SGI. For $\dot x = -(k_1 + k_2)x$, $y = x$, $x(0) = 1$: $V(s) = 1/(s + k_1 + k_2)$, only $k_1 + k_2$ is determined, so the structure is SU.

## Proof sketch

The output of an LTI system is determined by $\mathbf V$ and $\mathbf W$, and a rational function in lowest terms with monic denominator is uniquely determined by its coefficients, so these coefficients are a complete set of output invariants. If the structure is not generically minimal (pole–zero cancellation occurs for almost all $\boldsymbol\theta$), the unprocessed transfer functions have a spurious extra factor; cancelling it is required before reading off invariants, otherwise the test equations are wrong. The resulting polynomial equations are solved symbolically (e.g. by Gröbner bases); finitely many solutions mean SLI, the unique solution $\boldsymbol\theta' = \boldsymbol\theta$ means SGI.

## Sources

- Jason M. Whyte, "Model Structures and Structural Identifiability: What? Why? How?", in *MATRIX Book Series*, Springer International Publishing, 2021, 185–213, <https://doi.org/10.1007/978-3-030-62497-2_10>. Preprint version: arXiv:2101.06382 (2021), definitions of input–output and state-space systems, LTI and positive LTI structures, the structural identifiability definition, the transfer-matrix definition and degree property, and the identifiability-testing proposition, <https://doi.org/10.48550/arXiv.2101.06382>.
