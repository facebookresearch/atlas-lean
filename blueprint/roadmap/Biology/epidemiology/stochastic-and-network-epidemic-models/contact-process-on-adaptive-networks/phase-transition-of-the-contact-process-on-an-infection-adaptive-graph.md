# Phase transition of the contact process on an infection-adaptive random graph

**Models.** Vertices $[N]$; parameters: mean degree $\beta > 0$, infection rate $\lambda > 0$, rewiring rate $\kappa \ge 0$. Each infected vertex infects each current neighbour at rate $\lambda$ and recovers at rate $1$ (SIS infection, no immunity). The graph starts as an Erdős–Rényi graph with edge probability $\beta/N$. When a vertex *updates*, it deletes all its edges and reconnects to every other vertex independently with probability $\beta/N$.

- *Non-adaptive contact process:* every vertex updates at rate $\kappa$ (the dynamic Erdős–Rényi graph, stationary in law).
- *Adaptive contact process:* a vertex updates at rate $\kappa$ only while at least one of its neighbours is infected, modelling individuals who cut their contacts around infection.

With $|\xi_0| = 1$ and $I_\infty^{(N)}$ the set of vertices ever infected, the family is *subcritical* if $P(|I_\infty^{(N)}| > \varepsilon N) \to 0$ for every $\varepsilon > 0$, and *supercritical* if $\liminf_N P(|I_\infty^{(N)}| > \varepsilon N) > 0$ for some $\varepsilon > 0$.

**Statement (adaptive).**

1. If $\lambda\beta < 0.21$ or $(2\beta - 1)\lambda < \kappa$, then $(|I_\infty^{(N)}|)_N$ is tight; in particular the process is subcritical.
2. If

    $$
    \frac{\lambda\beta}{1 + 2\kappa + \lambda} > \sqrt{1 - \frac{\kappa(\lambda + \kappa)\bigl(1 - e^{-\beta\lambda/(\kappa + \lambda)}\bigr)}{(1+\kappa)(1 + 2\kappa + \lambda)}},
    $$

    the process is supercritical; in particular $\lambda\beta > 1 + 2\kappa + \lambda$ suffices.

**Statement (non-adaptive).** For $\kappa$ large enough, the process is subcritical (with tight $|I_\infty^{(N)}|$) if $\lambda\beta < 1$ and supercritical if $\lambda\beta > 1$.

So adaptation moves the phase transition: in the non-adaptive model the threshold for fast rewiring is the mean-field value $\lambda\beta \approx 1$, independent of $\kappa$, while in the adaptive model the bounds above place any critical value of $\lambda\beta$ between about $(\kappa+\lambda)/2$ and $1 + 2\kappa + \lambda$, which suggests (but does not prove) that it grows linearly in $\kappa$.

## Proof depends on

- [Galton–Watson extinction criterion](../../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md)

## Expansion

Because rewiring happens only near infection, the infection can suppress its own spread and standard monotone couplings fail. The proof approximates the early epidemic by a contact process on an evolving forest: the infected neighbourhood is locally a tree, and an update of a vertex starts a new tree rooted at that vertex. Treating each new tree as an offspring of the old one turns the process into a Galton–Watson tree, which survives if and only if its mean offspring number exceeds one. Bounding this mean from above and below gives the two explicit conditions. In the non-adaptive case fast rewiring decorrelates neighbourhoods, so the infection behaves like a branching process with mean $\lambda\beta$.

## Sources

- John Fernley, Peter Mörters and Marcel Ortgiese, "The contact process on a graph adapting to the infection", Stochastic Processes and their Applications 183 (2025), 104596, <https://doi.org/10.1016/j.spa.2025.104596>; numbering as in arXiv:2312.06251: Definitions 2.1–2.3, Theorems 2.4 and 2.5.
