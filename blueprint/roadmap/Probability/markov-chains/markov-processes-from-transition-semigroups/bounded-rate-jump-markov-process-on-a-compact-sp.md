# Bounded-rate jump Markov process on a compact space by uniformization

Let $E$ be a compact metric space and $\mu$ a finite kernel on $E$ such that $x\mapsto\mu(x,\cdot)$ is weakly continuous and $\lambda=\sup_x\mu(x,E)<\infty$ ($\lambda=0$, the zero kernel, is allowed). Then:

- $Bf(x)=\int_E\bigl(f(y)-f(x)\bigr)\,\mu(x,dy)$ is a bounded operator on $C(E)$ with domain $D(B)=C(E)$, and $T_t=e^{tB}$ is a Feller semigroup on $C(E)$;
- put $\Lambda=1+\lambda>0$ and $K(x,\cdot)=\bigl(\mu(x,\cdot)+(\Lambda-\mu(x,E))\,\delta_x\bigr)/\Lambda$, a weakly continuous probability kernel (since $x\mapsto\mu(x,E)$ is continuous). Running $K$ on the jumps of a Poisson clock of rate $\Lambda$, as in [the uniformized pure-jump process](../construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md), gives a càdlàg Markov process $X$ with $T_tf(x)=\mathbb E_xf(X_t)$, and for every $f\in C(E)$

$$f(X_t)-f(X_0)-\int_0^tBf(X_s)\,ds$$

is a martingale. Since $\Lambda(K-I)=B$, any choice $\Lambda>\lambda$ gives the same law; the strictly positive choice $\Lambda=1+\lambda$ avoids dividing by zero when $\mu=0$.

For $\mu=0$: $\Lambda=1$, $K(x,\cdot)=\delta_x$, $B=0$ and $X_t=X_0$ for all $t$. Parent-independent mutation, $\mu(x,\cdot)=\frac\theta2\nu$ for a probability measure $\nu$ and $\theta\ge0$, is a case of the theorem, with $\theta=0$ the zero-rate case.

## Depends on

- [A Markov kernel run on a Poisson clock is a pure-jump Markov process](../construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md)

## Proof depends on

- [Exponential interarrivals give a Poisson process](../../point-processes/poisson-processes/is-poisson-process-count.md)
- [Markov chain construction theorem](../construction-of-markov-chains/markov-chain-construction.md) (Ionescu-Tulcea trajectories)
- [Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings](../../convergence-of-measures/skorokhod-space/skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md)

## Expansion

A proof page must establish: boundedness of $B$ on $C(E)$ and $Bf\in C(E)$ by weak continuity; the Feller property of $e^{tB}=e^{-\Lambda t}\sum_k(\Lambda t)^kK^k/k!$, using that $K$ maps $C(E)$ into itself and is positive and unital; the identification $T_tf(x)=\mathbb E_xf(X_t)$ by conditioning on the number of clock rings; the Dynkin martingale; independence of the law from $\Lambda>\lambda$; and the two examples.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Chapter 4 (jump processes with bounded generators).
- J. R. Norris, *Markov Chains*, Cambridge University Press (1997), <https://www.statslab.cam.ac.uk/~jrn10//Markov/> (uniformization).
