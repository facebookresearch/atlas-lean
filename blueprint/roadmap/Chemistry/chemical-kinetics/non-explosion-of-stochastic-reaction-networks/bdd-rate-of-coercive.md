# Total propensity is bounded on sublevel sets of a coercive function

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) with a finite set $S$ of
species, a finite set of reactions and [total propensity](total-rate.md) $\lambda$. Let
$V : \mathbb{N}^S \to \mathbb{R}$ bound the total molecule count from above:
$\sum_{s \in S} x_s \le V(x)$ for every state $x$. Then for every real $m$ there is a $K$ with
$\lambda(x) \le K$ for all states $x$ with $V(x) < m$: the condition $V(x) < m$ forces
$x_s \le \lceil m \rceil$ for every species $s$, and only finitely many states satisfy this.
