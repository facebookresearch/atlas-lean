# Weak-mutation limit justifies the origination–fixation chain

This node covers the limit theorem that connects a finite Moran population with rare mutation to the [origination–fixation rate model](../fixation-flux-weak-mutation-chain-is-reversible.md).

Fix $N\ge1$, a finite type set $G$, fitnesses $f(g)>0$ and a symmetric mutation kernel $m(g,h)=m(h,g)\ge0$ for $g\ne h$ with $\sum_{h\ne g}m(g,h)\le1$. The clock is fixed as follows: Moran events occur at constant total rate $N$ per unit time, independently of the population's fitness; at each event a parent is chosen with probability proportional to fitness, its offspring mutates with probability $\mu$ to type $h$ with probability $m(g,h)$ (and otherwise keeps the parent's type $g$), and the offspring replaces an individual chosen uniformly from the population. Mutation is allowed in every state, monomorphic or not. From the monomorphic state of type $g$, mutant births of type $h$ arrive at rate $N\mu\,m(g,h)$, and a single mutant fixes with the [Moran fixation probability](../../population-genetics/moran-model/moran-fixation.md) $\varphi_1(f(h)/f(g))$, where $\varphi_1(r)=(1-r^{-1})/(1-r^{-N})$ for $r\ne1$ and $\varphi_1(1)=1/N$.

Two generators on $G$ are kept distinct: the physical-time origination–fixation rates $q_{\mathrm{phys}}(g,h)=N\mu\,m(g,h)\,\varphi_1(f(h)/f(g))$, which are those of the [reversible rate model](../fixation-flux-weak-mutation-chain-is-reversible.md) with stationary law proportional to $f^{N-1}$, and the accelerated rates $q_{\mathrm{acc}}(g,h)=m(g,h)\,\varphi_1(f(h)/f(g))$, both with diagonal minus the off-diagonal row sum. Let $L_t$ be the type of the most recently visited monomorphic state, with $L_0=g_0$ monomorphic. The target theorem: as $\mu\to0$ with $N$ fixed, the finite-dimensional distributions of $(L_{t/(N\mu)})_{t\ge0}$ converge to those of the continuous-time Markov chain with generator $q_{\mathrm{acc}}$ started at $g_0$. It is the case $\varepsilon=N\mu$ of the [finite-state rare-transition limit](finite-state-rare-transition-limit-for-the-last.md), with $R$ the monomorphic states, $T$ the polymorphic states, $Q_0$ the mutation-free Moran generator and $Q_1$ the coefficient of $\mu$ in the generator divided by $N$; mutation in polymorphic states enters only the rows of $T$ in $Q_1$ and does not change $q_{\mathrm{acc}}$.

A clock in which each individual reproduces at rate $f$, with total intensity $Nf(g)$ in the monomorphic state $g$, would give accelerated rates $f(g)\,m(g,h)\,\varphi_1(f(h)/f(g))$ and a different stationary law; it is not the model here. For example, with $N=1$, two types of equal fitness $2$ and $m(0,1)=1$, the constant-rate clock gives the physical type-change rate $\mu$ and the accelerated rate $1=m\,\varphi_1$, since $\varphi_1=1$; the fitness-dependent clock would give $2\mu$.

## Depends on

- [Reversibility of the Moran origination–fixation rate model](../fixation-flux-weak-mutation-chain-is-reversible.md)
- [Fixation probability of the Moran process](../../population-genetics/moran-model/moran-fixation.md)
- [Finite-state rare-transition limit for the last-visited absorbing state (Schur-complement form)](finite-state-rare-transition-limit-for-the-last.md)

## Expansion

An expansion states and proves separately:

- the decomposition $Q_{N\mu}=Q_0+N\mu\,Q_1$ of the Moran generator, with $Q_0$ having absorbing monomorphic states reached almost surely from every polymorphic state, and the computation $\bar q=q_{\mathrm{acc}}$ from the rows of $Q_1$ at monomorphic states and the absorption probabilities $\varphi_1$, $1-\varphi_1$ of a single mutant;
- the trace and last-fixed-type conventions and the finite-dimensional mode of convergence;
- the $N=1$ example, where there are no polymorphic states;
- the remark that the physical generator is $N\mu$ times the accelerated one, so the stationary law and reversibility are those of the rate model.

The cited sources do not state this fixed-$N$ limit: Champagnat's theorem concerns a logistic birth–death model with population size $K\to\infty$ jointly with $\mu\to0$, and Sella and Hirsh analyse the stationary law of the origination–fixation chain. A statement-level source, or a restatement as Champagnat's theorem, is an open obligation.

Prerequisites:

- [Reversibility of the Moran origination–fixation rate model](../fixation-flux-weak-mutation-chain-is-reversible.md)
- [Finite-state rare-transition limit for the last-visited absorbing state (Schur-complement form)](finite-state-rare-transition-limit-for-the-last.md)

## Sources

- N. Champagnat, *A microscopic interpretation for adaptive dynamics trait substitution sequence models*, Stochastic Processes and their Applications 116 (2006), 1127–1160, <https://ideas.repec.org/a/eee/spapps/v116y2006i8p1127-1160.html> (trait substitution sequence limit; background).
- G. Sella and A. E. Hirsh, *The application of statistical physics to evolutionary biology*, Proceedings of the National Academy of Sciences USA 102 (2005), 9541–9546, <https://pubmed.ncbi.nlm.nih.gov/15980155/> (weak-mutation regime; background).
