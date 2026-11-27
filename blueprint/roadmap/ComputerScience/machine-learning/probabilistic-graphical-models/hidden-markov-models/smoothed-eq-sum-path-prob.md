# Smoothed posterior as a sum over state paths

Let $g$ be a hidden Markov model with states $\{0, \dots, n - 1\}$ and weights in a semifield $K$,
let $x_0, x_1, \dots$ be observations, $T \in \mathbb{N}$, $t \le T$ and $s$ a state. The
[smoothed weight](smoothed.md) $\gamma_{t, T - t}(s)$ equals

$$\frac{\sum_{w \,:\, w_t = s} p_T(w)}{L_T},$$

the total joint weight $p_T(w)$ of the state paths $w = (w_0, \dots, w_T)$ through $s$ at time $t$
and the observations $x_0, \dots, x_T$, divided by the likelihood $L_T$ of $x_0, \dots, x_T$ (and
$0$ if $L_T = 0$).
