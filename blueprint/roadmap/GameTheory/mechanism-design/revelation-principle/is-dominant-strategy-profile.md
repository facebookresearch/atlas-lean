# Dominant-strategy profile

Let $I$ be a set of agents; agent $i$ has a set $\Theta_i$ of types and a set $X_i$ of actions, and $O$ is a set of outcomes. A mechanism is a map $g : \prod_i X_i \to O$; a direct mechanism is a map $f : \prod_i \Theta_i \to O$. For a profile $x$ and $a \in X_i$, $(a, x_{-i})$ is $x$ with its $i$-th entry replaced by $a$.
For private-value utilities $u_i(\theta_i, o) \in \mathbb{R}$, a strategy profile $s$, where agent $i$ of type
$\theta_i$ plays $s_i(\theta_i) \in X_i$, is a profile of dominant strategies in $g$ if whatever the others
play, $s_i(\theta_i)$ is a best action for agent $i$ of type $\theta_i$: for every agent $i$, type
$\theta_i$, action profile $x$ and action $a \in X_i$,

$$u_i\bigl(\theta_i, g(a, x_{-i})\bigr) \le u_i\bigl(\theta_i, g(s_i(\theta_i), x_{-i})\bigr)$$

(Nisan 2007, Definition 9.24 and the definition of dominant-strategy implementation in §9.4.2).

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Definition 9.24 and §9.4.2.
