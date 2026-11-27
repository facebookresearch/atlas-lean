# Convergence to a stationary trait distribution under random mating

Individuals of a hermaphroditic population carry a phenotypic trait in a closed interval $F \subseteq \mathbb R$ with nonempty interior. An offspring of parents with traits $x, y$ has trait distributed according to an **inheritance kernel** $K(x,y,dz)$: a Borel probability measure on $F$, symmetric in $(x,y)$, with $\int_F |z|\,K(x,y,dz) \le c_1 + c_2|x| + c_3|y|$ and

$$\int_F z\,K(x,y,dz) = \frac{x+y}{2}$$

(the offspring mean is the midparent value). In the large-population limit of the individual-based model with constant mating rate $p$, natural death rate $D$, interaction rate $I$ and competition kernel $U$, the total mass converges to the carrying capacity $(p - D)/(IU)$ whenever $D < p$ (and the population goes extinct if $D \ge p$). On this attractor, after normalizing mass and time, the trait distribution $\mu_t \in \mathcal P(F)$ under random mating solves

$$\frac{\partial}{\partial t}\mu_t + \mu_t = \mathcal P\mu_t, \qquad (\mathcal P\mu)(dz) = \int_F\int_F K(x,y,dz)\,\mu(dx)\,\mu(dy).$$

Let $\mathcal M_{\alpha,q}$ be the probability measures on $F$ with finite $\alpha$-th absolute moment and mean $q$, equipped with the Wasserstein-1 distance $d(\mu,\nu) = \int_F |\Phi(x)|\,dx$, where $\Phi$ is the distribution function of $\mu - \nu$. Write $\mathcal K(x,y,z) = K(x,y,F \cap (-\infty,z])$. The mean is conserved: $\int z\,(\mathcal P\mu)(dz) = q$ for $\mu \in \mathcal M_{1,q}$.

**Theorem.** Fix $q \in F$ and suppose

1. for all $y,z$, $\mathcal K(x,y,z)$ is absolutely continuous in $x$ and, for all $a,b,y \in F$, $\int_F \big|\partial_x\mathcal K(a,y,z) - \partial_x\mathcal K(b,y,z)\big|\,dz < 1$;
2. there are $\alpha > 1$, $L < 1$ and $C \ge 0$ with $\int_F |x|^\alpha\,\mathcal P\mu(dx) \le C + L\int_F |x|^\alpha\,\mu(dx)$ for all $\mu \in \mathcal M_{\alpha,q}$.

Then for every $\mu_0 \in \mathcal M_{1,q}$ there is a unique solution in $\mathcal M_{1,q}$, there is a unique $\mu^* \in \mathcal M_{1,q}$ with $\mathcal P\mu^* = \mu^*$, and $\mu_t \to \mu^*$ in $\mathcal M_{1,q}$. If moreover $K(x,y,dz) = k(x,y,z)\,dz$ with $k$ bounded and continuous, then $\mu^*$ has a bounded continuous density $u_*$, and $\mu_t = e^{-t}\mu_0 + \nu_t$ with $\nu_t$ having bounded continuous densities converging uniformly to $u_*$.

**Example.** If the offspring trait is $\frac{x+y}{2} + Z\frac{|x-y|}{2}$ with $Z$ independent of variance $D(Z) < 1$, the trait variance obeys $\frac{d}{dt}\mathrm{Var}(\mu_t) = -\tfrac12(1 - D(Z))\,\mathrm{Var}(\mu_t)$, so $\mu_t$ converges weakly to the point mass at the conserved mean.

## Expansion

The key estimate is a strict contraction of $\mathcal P$ in Wasserstein distance on $\mathcal M_{1,q}$: writing $d(\mathcal P\mu, \mathcal P\nu)$ through distribution functions and integrating by parts in $x$, condition 1 gives $2\int_F|\int_F \mathcal K(x,y,z)\,\Phi(dx)|\,dz < \int_F |\Phi|$, hence $d(\mathcal P\mu,\mathcal P\nu) < d(\mu,\nu)$ for $\mu \neq \nu$ with equal means. The evolution $\mu_t = e^{-t}\mu_0 + \int_0^t e^{-(t-s)}\mathcal P\mu_s\,ds$ then strictly decreases distances between solutions. Condition 2 keeps orbits in a set with bounded $\alpha$-moment, which is relatively compact in $\mathcal M_{1,q}$; a strictly contracting flow on a compact invariant set has a unique fixed point that attracts every orbit. Regularity of $\mu^*$ follows from the smoothing of $\mathcal P$ when $K$ has a bounded continuous density.

## Sources

- Ryszard Rudnicki, Paweł Zwoleński, "Model of phenotypic evolution in hermaphroditic populations", *Journal of Mathematical Biology* 70 (2015), 1295–1321, <https://doi.org/10.1007/s00285-014-0798-3>; preprint arXiv:1309.3243, <https://doi.org/10.48550/arXiv.1309.3243>. Numbering of the arXiv version: Section 2 (mating, inheritance kernel conditions, competition and death), Section 4 (Proposition 1, carrying capacity, equation on the global attractor, the variance example), Section 5 (Wasserstein distance, Lemma 1, Theorem 3, Lemmas 2–5, Theorem 4).
