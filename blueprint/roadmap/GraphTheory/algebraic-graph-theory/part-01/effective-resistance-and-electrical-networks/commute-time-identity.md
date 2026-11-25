# Commute-time identity

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+ \ne e^-$ in $V$ (a finite loopless multigraph) with connected [underlying graph](../oriented-incidence-matrices/underlying-graph.md), and let $w : E \to (0, \infty)$ be conductances. For $a, z \in V$ let $h_a$ and $h_z$ solve the [first-step equations](is-hitting-time-solution.md) of the hitting times of $a$ and of $z$. Then

$$h_z(a) + h_a(z) = \gamma\, R_{\mathrm{eff}}(a, z), \qquad \gamma = 2 \sum_{e \in E} w_e = \sum_{x \in V} \pi(x),$$

where $R_{\mathrm{eff}}$ is the [effective resistance](effective-resistance.md) and $\pi$ the [weighted degree](../../part-02/conductance-and-cheeger-s-inequality/weighted-degree.md) (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Corollary 2.21, due to Chandra, Raghavan, Ruzzo, Smolensky and Tiwari). For $a = z$ both sides are $0$.

The source's commute time is $\mathbb{E}_a[\tau_z] + \mathbb{E}_z[\tau_a]$ for the network random walk; on a connected loopless multigraph the expected hitting times are the unique solutions of the first-step equations, so this identity is the source's. It follows by linear algebra: a solution $h_z$ satisfies $L h_z = \pi - \gamma \delta_z$, so $(h_z - h_a)/\gamma$ is a potential for a unit current from $a$ to $z$.

## Background

- [Hitting times of finite continuous-time Markov chains](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/README.md): the first-step characterisation of expected hitting times in continuous time.
