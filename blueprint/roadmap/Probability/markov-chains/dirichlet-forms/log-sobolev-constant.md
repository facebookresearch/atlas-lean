# Log-Sobolev constant of a finite Markov kernel

Let $S$ be a finite set, $P$ a real $S \times S$ matrix, $\mathcal E_{\pi, P - I}$ the [form](form.md)
of the generator $P - I$ and $\mathcal L_\pi$ the [entropy-like functional](entropy-functional.md).
For a probability vector $\pi$ on a finite state space (here $S$: $\pi \ge 0$, $\sum_x \pi(x) = 1$),

$$\alpha(P, \pi) = \inf \Bigl\{ \frac{\mathcal E_{\pi, P - I}(f, f)}{\mathcal L_\pi(f)} : f : S \to \mathbb{R},\ \mathcal L_\pi(f) \ne 0 \Bigr\},$$

the infimum being read as $0$ when the set is empty or unbounded below. When $\alpha(P, \pi) > 0$ (so that some $f$ has $\mathcal L_\pi(f) \ne 0$), $1/\alpha$
is the best constant $C$ in $\mathcal L_\pi(f) \le C\, \mathcal E_{\pi, P - I}(f, f)$.

## Background

- [Logarithmic Sobolev inequality](../../concentration-inequalities/transport-cost-inequalities/satisfies-log-sobolev.md): the version on metric measure spaces used for the
  Otto–Villani theorem. Substituting $f = g^2 / \|g\|_2^2$ in its inequality
  $2\alpha \int f \log f \le \int |\nabla f|^2 / f$ gives $\mathcal L(g) \le (2/\alpha) \int |\nabla g|^2$,
  so its constant $\alpha$ corresponds to the constant $\alpha/2$ here when the Dirichlet form is
  $\int |\nabla g|^2$.
- [Gross' logarithmic Sobolev inequality](../../concentration-inequalities/transport-cost-inequalities/kl-div-with-density-std-gaussian-le.md): the Gaussian model case.

## Sources

- P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*, Annals of Applied Probability 6 (1996), 695–750, equations (1.7) and (3.1).
