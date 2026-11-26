# Large-population limit of the birth–death–competition process

**Model.** Fix a trait space $\mathcal{X}$ and a carrying-capacity parameter $K \in \mathbb{N}$. Each individual with trait $x$ gives birth at rate $b(x) \ge 0$; the offspring is a mutant with probability $p(x)$ (or $u_K p(x)$ when mutation probabilities are scaled with $K$), its trait then drawn from a mutation kernel $m(x,dy)$, and otherwise a clone. Each individual dies at the natural rate $d(x) \ge 0$ plus a competition rate $\frac1K \sum_j c(x, x_j)$ summed over the other individuals. The rescaled population is the finite point measure $\nu^K_t = \frac1K \sum_{i=1}^{N_t} \delta_{x_i(t)} \in \mathcal{M}_F(\mathcal{X})$. For a monomorphic population of trait $x$ with $b(x)>d(x)$ the logistic equilibrium is $\bar n(x) = (b(x)-d(x))/c(x,x)$, and the *invasion fitness* of a mutant $y$ against coexisting residents $\mathbf{x}=(x_1,\dots,x_d)$ at equilibrium $\bar n(\mathbf{x})$ is $f(y,\mathbf{x}) = b(y) - d(y) - \sum_{i} c(y,x_i)\, \bar n_{x_i}(\mathbf{x})$.

**Theorem (deterministic large-population limit).** Assume the standing boundedness assumptions on $b, d, c$, fix the mutation probability $p$ and kernel $m$ (no scaling with $K$), suppose $\nu^K_0 \to \xi_0$ in law for the weak topology on $\mathcal{M}_F(\mathcal{X})$ with $\xi_0$ a deterministic finite measure, and $\sup_K \mathbb{E}[\langle \nu^K_0, 1\rangle^2] < \infty$. Then for every $T>0$, $\nu^K \to \xi$ in law in $\mathbb{D}([0,T], \mathcal{M}_F(\mathcal{X}))$, where $\xi \in C([0,T], \mathcal{M}_F(\mathcal{X}))$ is deterministic and is the unique solution with $\sup_{t \le T}\langle \xi_t, 1\rangle < \infty$ of the weak integro-differential equation: for all bounded measurable $h:\mathcal{X}\to\mathbb{R}$,
$$\langle \xi_t, h\rangle - \langle \xi_0, h\rangle = \int_0^t \!\! \int_{\mathcal{X}} \xi_s(dx)\, p(x) b(x) \int m(x,dy)\, h(y)\, ds + \int_0^t \!\! \int_{\mathcal{X}} \xi_s(dx)\, h(x)\Big( (1-p(x)) b(x) - d(x) - \int_{\mathcal{X}} \xi_s(dy)\, c(x,y)\Big) ds.$$
For finitely many traits without mutation this is the competitive Lotka–Volterra system $\dot n_x = n_x\big(b(x)-d(x)-\sum_y c(x,y) n_y\big)$.

## Expansion

The process solves the martingale problem of its generator $\mathcal{L}^K$; a uniform second-moment bound on the total mass gives tightness, the martingale parts have quadratic variation of order $1/K$ and vanish, and every limit point satisfies the weak equation, whose solution is unique by a Gronwall argument in total variation.

## Sources

- A. Bovier, A. Kraut, "Stochastic individual-based models", arXiv:2607.11520, Chapter 2, Theorem 2.8 (law of large numbers of Fournier and Méléard). <https://doi.org/10.48550/arXiv.2607.11520>
