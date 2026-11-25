# The L^p norm tends to the essential supremum

Let $\mu$ be a finite measure and $f$ a real essentially bounded function, $f \in L^\infty(\mu)$. Then
$\|f\|_{L^p(\mu)} \to \|f\|_{L^\infty(\mu)}$ as the real exponent $p$ tends to $\infty$.

## Idea

The essential supremum is the limit of the $L^p$ norms, which is why it is written $\|f\|_\infty$.
If $\mu = 0$ all these norms vanish. Otherwise, from above,
$\|f\|_p \le \mu(\alpha)^{1/p} \|f\|_\infty$ with $\mu(\alpha)^{1/p} \to 1$; from below, for
$0 \le t < \|f\|_\infty$ the set $\{|f| > t\}$ has positive measure $m$, so
$\|f\|_p \ge t\, m^{1/p} \to t$. The lower bound needs no a priori boundedness, and the second
statement records its consequence on $[0, 1]$: bounds on all the $L^p$ norms bound the $L^\infty$
norm.

## Statements

- [The $L^p$ norm tends to the $L^\infty$ norm](tendsto-e-lp-norm-at-top-e-lp-norm-top-o.md)
- [Uniform $L^p$ bounds on $[0,1]$ give the same $L^\infty$ bound](e-lp-norm-top-le-of-forall-one-le-e-lp-n.md): the lower half of the limit as a bound: on $[0, 1]$, $L^p$ bounds uniform in $p \ge 1$ bound the $L^\infty$ norm, with no a priori boundedness.
