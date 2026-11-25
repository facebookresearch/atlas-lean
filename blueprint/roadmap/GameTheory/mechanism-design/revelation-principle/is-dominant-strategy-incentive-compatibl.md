# Dominant-strategy incentive compatibility

Let $I$ be a set of agents; agent $i$ has a set $\Theta_i$ of types and a set $X_i$ of actions, and $O$ is a set of outcomes. A mechanism is a map $g : \prod_i X_i \to O$; a direct mechanism is a map $f : \prod_i \Theta_i \to O$. For a profile $x$ and $a \in X_i$, $(a, x_{-i})$ is $x$ with its $i$-th entry replaced by $a$.
For private-value utilities $u_i(\theta_i, o) \in \mathbb{R}$, the direct mechanism $f$, which maps each
profile of reported types to an outcome, is dominant-strategy incentive compatible (strategy-proof) if
truthful reporting is optimal for every agent whatever the others report: for every agent $i$, type profile
$\theta$ and report $\theta_i' \in \Theta_i$,
$u_i\bigl(\theta_i, f(\theta_i', \theta_{-i})\bigr) \le u_i(\theta_i, f(\theta))$ (Nisan 2007, Definition
9.15, with payments absorbed into the outcome).

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Definition 9.15.
