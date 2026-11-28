# Random killing in the kill-the-least-fit model of influenza evolution

**Model.** Fix a mutation rate $\lambda > 0$ and a random-killing probability $r \in [0,1]$. The number of virus types $X(t)$ is a birth–death chain on $\{1, 2, \dots\}$ with transitions $n \to n+1$ at rate $n\lambda$ ($n \ge 1$) and $n \to n-1$ at rate $n$ ($n \ge 2$). Each newly created type receives a fitness drawn independently from the uniform distribution on $(0,1)$. At a death event the type removed is, with probability $r$, chosen uniformly among the living types and, with probability $1-r$, the type of minimal fitness. Start from a single type with uniform fitness and age $0$, and let

- $\phi_t$ = the maximal fitness among types alive at time $t$,
- $a_t$ = the age at time $t$ of the type achieving $\phi_t$.

**Theorem.** Let $\mathcal E$ denote a mean-one exponential random variable.

1. ($r = 0$.) For every $\lambda > 0$, $\phi_t \to 1$ almost surely. If $\lambda > 1$, then $a_t \Rightarrow \frac{1}{\lambda - 1}\,\mathcal E$ as $t \to \infty$. (For $\lambda \le 1$ one has instead $a_t / t \Rightarrow U$ with $U$ uniform on $(0,1)$.)
2. ($r > 0$, $\lambda < 1$.) Both $\phi_t$ and $a_t$ converge in distribution as $t \to \infty$ to nondegenerate limit laws; in particular the maximal fitness does not tend to $1$ and the age of the fittest type stays tight.
3. ($r > 0$, $\lambda \ge 1$.) $\phi_t \to 1$ in probability.

Thus for $\lambda < 1$ any positive amount of random killing changes the qualitative behaviour: without it the fittest type has age of order $t$, with it the age has a stationary limit.

## Expansion

For $r = 0$ and $\lambda > 1$, $X(t)$ is a supercritical linear birth–death process, so $N(t)e^{-(\lambda-1)t}$ converges almost surely to a positive limit; types are only removed from the bottom of the fitness order, so the current maximum is the best of all types ever born, and the time since the most recent record among roughly $e^{(\lambda-1)t}$ uniform draws is asymptotically exponential with rate $\lambda - 1$. For $r > 0$ and $\lambda < 1$, $X(t)$ is positive recurrent and the process regenerates: the times $R_1$ at which the population returns to a single type and that type is replaced form a renewal sequence with exponential tails ($P(R_1 > t) \le Ce^{-\gamma t}$), and the renewal identities $P(\phi_t \le v, R_1 \le t) = \int_0^t P(R_1 \in ds)\, P(\phi_{t-s} \le v)$ (and likewise for $a_t$) yield convergence to nondegenerate limits by the key renewal theorem. For $\lambda \ge 1$ the number of types is not positive recurrent and a monotone coupling of fitness sets (adding a common element or deleting the smallest element preserves the stochastic order of maxima) shows that the maximal fitness is eventually at least that of a system whose maximum tends to $1$.

## Sources

- J. Theodore Cox, Rinaldo B. Schinazi, "A stochastic model for the evolution of the influenza virus", *Markov Processes and Related Fields* 20 (2014), 155–166; preprint arXiv:1302.2362, <https://doi.org/10.48550/arXiv.1302.2362>. Numbering of the arXiv version: Section 1 (model; Theorem 1 restating the $r=0$ results; Theorems 2–4), Section 2 (Lemma 1), Section 3 (Lemmas 2–3), Section 4 (Lemma 4).
