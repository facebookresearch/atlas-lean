# Epidemic state of a configuration at generation n

For a finite set $S_0$ of initially susceptible individuals of the population $\{0, \dots, N-1\}$, a
[configuration](config.md) $w = (w_1, w_2)$ and $n \in \mathbb{N}$, the epidemic state of $w$ at
generation $n$ is the [state](../branching-process-approximation-of-early-epidemi/epi.md)
$(I_n, D_n)$ of the epidemic with offspring numbers $\xi_{m,i} = w_1(m, i)$, contact targets
$U_j = w_2(j)$ and initially susceptible set $S_0$: $I_n$ infectives in generation $n$ and $D_n$
contacts made by generations $0, \dots, n-1$.
