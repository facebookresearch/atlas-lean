# Posterior expected number of correctly decoded states

Let $g$ be a hidden Markov model with states $\{0, \dots, n - 1\}$ and weights in a semifield $K$,
let $x_0, x_1, \dots$ be observations and $T \in \mathbb{N}$, write $p_T(w)$ for the joint weight
of a state path $w = (w_0, \dots, w_T)$ and $x_0, \dots, x_T$, and $L_T$ for the likelihood of
$x_0, \dots, x_T$. The posterior expected number of correctly decoded states of a path $z$ is

$$\sum_{w} \frac{p_T(w)}{L_T} \, \bigl|\{t \le T : w_t = z_t\}\bigr|,$$

the sum running over all state paths $w$ of length $T + 1$. When the weights are probabilities
and the likelihood is positive, this is the expectation under the posterior law of the path; for
$L_T = 0$ it is $0$ (division by $0$ gives $0$), as is every smoothed weight.
