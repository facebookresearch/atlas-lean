# The Baum-Welch log-likelihood is the HMM log-likelihood

Let $S$ and $O$ be finite sets,
let $T$ be a natural number, and let $x_1, \dots, x_N$ be sequences
$x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in $O$. For every valid hidden Markov model $h$
on states $S$ and observations $O$, the log-likelihood of its EM model (latent state paths
$(z_0, \dots, z_T)$, joint the path weight) on these data equals $\sum_{n=1}^{N} \log L_h(x_n)$,
where $L_h(x_n)$ is the likelihood of the observations $x_{n,0}, \dots, x_{n,T}$ under $h$: the
total path weight over all state paths $(z_0, \dots, z_T)$.
