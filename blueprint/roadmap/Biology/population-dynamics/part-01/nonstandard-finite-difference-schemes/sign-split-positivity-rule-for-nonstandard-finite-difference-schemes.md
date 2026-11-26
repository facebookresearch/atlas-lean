# Sign-split positivity rule for nonstandard finite difference schemes

**Setting.** Population models $\dot\xi=f(\xi,K)$ must keep densities non-negative, which explicit Euler schemes fail to do for large steps. A nonstandard finite difference (NSFD) scheme in Mickens' sense replaces the step $\Delta t$ by a denominator function

$$\phi(\Delta t)=\frac{1-e^{-q\Delta t}}{q}=\Delta t+O(\Delta t^2),\qquad 0<\phi(\Delta t)<\frac1q,$$

with $q\ge\max_\lambda\lambda^2/(2|\operatorname{Re}\lambda|)$ over the Jacobian eigenvalues $\lambda$ with $\operatorname{Re}\lambda\ne0$, and replaces nonlinear terms by nonlocal discrete representations, giving $(\xi_{n+1}-\xi_n)/\phi(\Delta t)=F(\xi_n,\xi_{n+1},K)$. A scheme that preserves positivity and the local stability of equilibria is called *positive and elementary stable nonstandard* (PESN).

**Theorem.** Suppose a right-hand side term has the form

$$f(\xi,K)=(-1)^p\,\xi^m\,g(\xi,K),\qquad m\in\mathbb N^+,\ p\in\{0,1\},$$

with $g>0$ for all $\xi$ and positive parameters $K$. Then the discretization

$$F(\xi_n,\xi_{n+1},K)=\frac{(-1)^p}{2}\Big[\big(1-(-1)^{p+1}\big)\xi_n^m+\big(1-(-1)^p\big)\xi_n^{m-1}\xi_{n+1}\Big]g(\xi_n,K)$$

preserves positivity: explicitly,

$$\xi_{n+1}=\xi_n+\phi(\Delta t)\,g(\xi_n,K)\,\xi_n^m\quad(p=0),\qquad \xi_{n+1}=\frac{\xi_n}{1+\phi(\Delta t)\,g(\xi_n,K)\,\xi_n^{m-1}}\quad(p=1),$$

so $\xi_n\ge0$ implies $0\le\xi_{n+1}(p=1)\le\xi_n\le\xi_{n+1}(p=0)$ for every step size.

In words: gain terms are kept explicit, while each loss term is made implicit in exactly one factor of the state, which turns the update into a ratio of positive quantities. Applied term by term, this yields positivity-preserving NSFD versions of multi-species models, for example a within-season aphid–ant–ladybird model with cumulative-density self-regulation of aphids, ant–aphid mutualism and ladybird predation.

## Expansion

Substituting $F$ into the difference equation and solving the resulting linear equation for $\xi_{n+1}$ gives the two explicit updates. For $p=0$ the bracket equals $2\xi_n^m$ and the update adds a non-negative increment. For $p=1$ the bracket equals $2\xi_n^{m-1}\xi_{n+1}$, so the loss is proportional to the new value and the update divides $\xi_n$ by a number at least $1$. For a pure loss $\dot x=-x^3/(x^2+\theta)$ this gives $x_{n+1}=x_n(x_n^2+\theta)/\big(x_n^2(1+\phi(\Delta t))+\theta\big)$. Combining the rule with the denominator function chosen from the Jacobian spectrum keeps the fixed points and their linear stability, which is how elementary stability is checked.

## Sources

- Gianluca Gabbriellini, "Aphids, Ants and Ladybirds: a mathematical model predicting their population dynamics", arXiv:1905.05244 (2019), Section 2 (continuous AAL model), Section 3 (NSFD rules, Definition 3.1 and Theorem 3.1, worked example), Section 4 (stability of the discrete fixed points), <https://doi.org/10.48550/arXiv.1905.05244>.
