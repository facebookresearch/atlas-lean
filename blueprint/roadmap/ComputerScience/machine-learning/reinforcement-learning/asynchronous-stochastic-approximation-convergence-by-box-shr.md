# Asynchronous stochastic approximation: convergence by box shrinking

This node collects the two convergence theorems of Tsitsiklis for the asynchronous iteration
$x_i(t+1) = x_i(t) + \alpha_i(t)\bigl(F_i(x^i(t)) - x_i(t) + w_i(t)\bigr)$ in $\mathbb{R}^n$, where component
$i$ is updated with step size $\alpha_i(t)$ (zero when not updated), possibly from outdated
information $x^i(t)$, and $w_i(t)$ is noise.

## Expansion

A sound expansion has separate pages for:

1. **Common hypotheses** (Tsitsiklis, Assumptions 1–3): every delayed component index tends to
   infinity (outdated information is eventually refreshed); with respect to a filtration
   $\mathcal{F}(t)$ describing the history, step sizes are $\mathcal{F}(t)$-measurable, the noise has
   zero conditional mean and conditional second moment at most $A + B\max_j \max_{\tau \le t}
   \lvert x_j(\tau) \rvert^2$; for every $i$, $\sum_t \alpha_i(t) = \infty$ and
   $\sum_t \alpha_i(t)^2 \le C$ for a deterministic constant $C$.
2. **Convergence under monotonicity** (Theorem 2): if in addition $F$ is monotone and continuous, has
   a unique fixed point $x^*$, and satisfies $F(x) - re \le F(x - re) \le F(x + re) \le F(x) + re$ for
   every $r > 0$ ($e$ the all-ones vector) (Assumption 4), and the iterates are bounded almost surely,
   then $x(t) \to x^*$ almost surely.
3. **Convergence under weighted pseudocontraction** (Theorem 3): if in addition there are a positive
   weight vector $v$ and $0 \le \beta < 1$ with $\lVert F(x) - x^* \rVert_v \le \beta \lVert x - x^* \rVert_v$
   for every $x$ (Assumption 5), then $x(t) \to x^*$ almost surely. This is pseudocontraction toward
   the fixed point, not a Lipschitz condition between arbitrary pairs.

The boundedness theorem used by item 3 is the separate prerequisite page below. Each page records the
exact form of the cited assumptions.

## Proof depends on

- [Boundedness of asynchronous stochastic-approximation iterates](boundedness-of-asynchronous-stochastic-approximation-iterate.md)

## Sources

- J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Machine Learning 16 (1994) 185–202, Section 2: the iteration, Assumptions 1–5 (pp. 188–189) and Theorems 2 and 3 (p. 189). <https://www.mit.edu/~jnt/Papers/J052-94-jnt-q.pdf>
