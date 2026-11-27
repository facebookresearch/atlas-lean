# Recurrence and stationary law of reaction networks within interacting compartments

**Model (RNIC).** A *reaction network within interacting compartments* $\mathcal{T} = (\mathcal{S}_\kappa, \mathcal{C}_\kappa, \mu)$ consists of a stochastic reaction network $\mathcal{S}_\kappa$ (a continuous-time Markov chain on $\mathbb{Z}^d_{\ge 0}$ with mass-action rates) run independently inside each of a varying number of compartments, together with compartment dynamics $\mathcal{C}_\kappa$: compartments arrive at rate $\kappa_I$ (inflow) with initial content drawn from a law $\mu$ on $\mathbb{Z}^d_{\ge 0}$, each compartment exits at rate $\kappa_E$, pairs of compartments merge at rate $\kappa_C$ (adding contents), and a compartment fissions at rate $\kappa_F$ (splitting contents). The *coarse-grained* state $N = (n_x)_{x \in \mathbb{Z}^d_{\ge 0}}$ counts the compartments with content $x$; $\|N\|_{\ell^1}$ is the number of compartments, which by itself is the Markov chain $\mathcal{C}_\kappa$ on $\mathbb{Z}_{\ge 0}$.

**Theorem.**
1. *(Explosivity.)* $\mathcal{T}$ is explosive iff the single-compartment network $\mathcal{S}_\kappa$ is explosive.
2. *(Recurrence.)* If $\mathcal{T}$ is non-explosive and $\kappa_E > 0$, a coarse-grained state $n$ is recurrent (respectively positive recurrent) iff $n$ is reachable from the empty state and the compartment number $\|n\|_{\ell^1}$ is recurrent (respectively positive recurrent) for $\mathcal{C}_\kappa$. The same holds for the full (ordered) representation of the contents.
3. *(Stationary law with inflow and exit only.)* Suppose $\mathcal{S}_\kappa$ is non-explosive (equivalently, by item 1, $\mathcal{T}$ is), $\kappa_F = \kappa_C = 0$ and $\kappa_E > 0$. Let $P_\mu(x,t)$ be the probability that $\mathcal{S}_\kappa$ started from $\mu$ is in state $x$ at time $t$, and

$$\alpha(x) = \int_0^\infty P_\mu(x,t)\,\kappa_E e^{-\kappa_E t}\,dt .$$

Then the unique stationary distribution of the coarse-grained model is

$$\pi(n) = \left(\prod_{x\in\mathbb{Z}^d_{\ge 0}} \frac{\alpha(x)^{n_x}}{n_x!}\right) e^{-\kappa_I/\kappa_E}\left(\frac{\kappa_I}{\kappa_E}\right)^{\|n\|_{\ell^1}},$$

that is, the number of compartments is Poisson$(\kappa_I/\kappa_E)$ and, given it, the contents are i.i.d. with law $\alpha$: the law of the chemistry at an independent exponential$(\kappa_E)$ age.

## Expansion

Exit at positive rate makes the empty state reachable from everywhere, so the chemistry cannot keep the chain away from it longer than the compartment process allows; recurrence of the whole system reduces to recurrence of the compartment count, proved with Foster–Lyapunov criteria ($\mathcal{L}V \le -1$ off a finite set for positive recurrence, a bounded $\mathcal{L}V \ge 0$ function for transience). In the inflow–exit case compartments form an $M/M/\infty$ queue whose customers carry independent copies of the chemistry; by stationarity of the queue, the ages of compartments present are i.i.d. exponential$(\kappa_E)$, so contents are mixtures of $P_\mu(\cdot, t)$ over exponential ages, and Poisson thinning by content gives the product form; one checks $\pi Q = 0$ directly.

## Sources

- D. F. Anderson and A. S. Howells, "Stochastic reaction networks within interacting compartments", *Bulletin of Mathematical Biology* 85(10) (2023), 87, Theorems 3.3, 4.5, 4.6, 4.8, 4.9 and 5.1, <https://doi.org/10.1007/s11538-023-01185-w> (preprint arXiv:2303.14093).
