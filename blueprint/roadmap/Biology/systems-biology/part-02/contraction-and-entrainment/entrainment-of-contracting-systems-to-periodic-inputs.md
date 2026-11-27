# Entrainment of contracting systems to periodic inputs

Let $|\cdot|$ be a vector norm on $\mathbb R^n$ with induced matrix norm $\|\cdot\|$, and define the associated *matrix measure* (logarithmic norm)

$$\mu(A) = \lim_{h \downarrow 0} \frac{\|I + hA\| - 1}{h}.$$

For the weighted norm $|x|_{1,P} = |Px|_1$ with $P$ nonsingular, $\mu_{1,P}(A) = \mu_1(PAP^{-1})$ and $\mu_1(A) = \max_j \bigl(a_{jj} + \sum_{i \ne j} |a_{ij}|\bigr)$. Consider $\dot x = f(t,x)$ with $f$ continuously differentiable in $x$, on a set $C \subseteq \mathbb R^n$ invariant for the flow. The system is *infinitesimally contracting with rate $c > 0$* on $C$ if

$$\mu\!\left(\frac{\partial f}{\partial x}(t,x)\right) \le -c \qquad \text{for all } t \ge 0,\ x \in C.$$

1. **Global contraction.** If $C$ is convex and the system is infinitesimally contracting with rate $c$, then any two solutions $x, z$ with $x(t_0) = \xi$, $z(t_0) = \zeta$ in $C$ satisfy

$$|x(t) - z(t)| \le e^{-c(t-t_0)}\, |\xi - \zeta| \qquad (t \ge t_0).$$

2. **Entrainment.** If moreover $C$ is closed and $f$ is $T$-periodic in $t$, i.e. $f(t+T,x) = f(t,x)$, then there is a unique periodic solution $\alpha$ of period $T$ in $C$, and every solution in $C$ satisfies $|x(t) - \alpha(t)| \to 0$ exponentially as $t \to \infty$.

Convexity can be weakened to *$K$-reachability*: any two points are joined by a curve in $C$ of length at most $K$ times their distance, which multiplies the bound in item 1 by $K$.

## Expansion

For item 1 join $\xi$ and $\zeta$ by the segment $\gamma(r) = \zeta + r(\xi - \zeta)$, let $\phi(t,r)$ be the solution started at $\gamma(r)$, and set $w(t,r) = \partial_r \phi(t,r)$. Then $\partial_t w = \frac{\partial f}{\partial x}(t,\phi)\, w$, and the defining property of the matrix measure gives $D^+ |w| \le \mu(\partial f/\partial x)\, |w| \le -c|w|$, so $|w(t,r)| \le e^{-c(t-t_0)}|\xi - \zeta|$. Integrating over $r \in [0,1]$ bounds $|x(t) - z(t)|$. For item 2 the period map $\Phi(\xi) = x(t_0 + T; t_0, \xi)$ is, by item 1, a contraction on the closed set $C$ with constant $e^{-cT} < 1$. By the Banach fixed-point theorem it has a unique fixed point, which is the initial value of the periodic solution, and the iterates of $\Phi$ from any initial value converge to it. Since the measure only needs to be negative in some norm, a weighted norm such as $|Px|_1$ with a diagonal $P$ is chosen to suit the Jacobian, which turns contraction into column diagonal dominance conditions.

## Sources

- G. Russo, M. di Bernardo, E. D. Sontag, "Global entrainment of transcriptional systems to periodic inputs", *PLoS Computational Biology* (2010), Results (Theorems 1–2, matrix measures, Eq. (17)) and Materials and Methods (Definition 1, Theorems 5–6, Lemma 1), <https://doi.org/10.1371/journal.pcbi.1000739> (PMC2855316).
