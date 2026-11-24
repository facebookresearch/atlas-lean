# Smoothed state weights

For a hidden Markov model with a finite set of states $S$ and
weights in a semifield $K$, observations $x_0, x_1, \dots$, times $t, k \in \mathbb{N}$ and a
state $s \in S$, the smoothed weight of $s$ at time $t$ is

$$\gamma_{t,k}(s) = \frac{\alpha_t(s)\,\beta_{k,t}(s)}{L_{t+k}},$$

where $\alpha_t(s)$ is the forward variable, $\beta_{k,t}(s)$ is the backward variable (the weight
of $x_{t+1}, \dots, x_{t+k}$ given the state $s$ at time $t$) and $L_{t+k}$ is the likelihood of
$x_0, \dots, x_{t+k}$. Division is that of $K$, so $\gamma_{t,k}(s) = 0$ when $L_{t+k} = 0$.

For nonnegative weights with stochastic rows and a positive likelihood this is the smoothing
posterior $P(z_t = s \mid x_0, \dots, x_{t+k})$ that the hidden state $z_t$ at time $t$ is $s$; for
general semifield weights it is only this ratio.
