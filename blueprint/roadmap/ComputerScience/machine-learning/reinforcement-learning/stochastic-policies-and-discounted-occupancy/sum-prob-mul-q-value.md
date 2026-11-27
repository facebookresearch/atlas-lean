# Averaged action values are the induced Bellman update

For a Markov decision process, a stochastic policy $\pi$, a function $V$ and a state $s$,

$$\sum_a \pi(a \mid s)\Bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') V(s')\Bigr) = r^\pi(s) + \gamma \sum_{s'} P^\pi(s,s') V(s').$$
