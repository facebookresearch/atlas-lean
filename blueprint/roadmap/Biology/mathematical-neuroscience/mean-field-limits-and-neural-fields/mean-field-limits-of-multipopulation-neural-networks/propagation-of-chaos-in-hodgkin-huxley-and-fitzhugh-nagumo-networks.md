# Propagation of chaos in Hodgkin–Huxley and FitzHugh–Nagumo networks

**Network.** $N$ neurons are divided into $P$ populations with sizes $N_\gamma$. Neuron $i$ in population $\alpha$ has state $X^{i,N}_t \in \mathbb R^d$ (membrane potential and gating or recovery variables, as in the [Hodgkin–Huxley model](../../hodgkin-huxley-model/README.md) or the [FitzHugh–Nagumo model](../../fitzhugh-nagumo-model/README.md)) and obeys

$$dX^{i,N}_t = f_\alpha(t, X^{i,N}_t)\,dt + \sum_{\gamma=1}^P \frac{1}{N_\gamma}\sum_{j\in\gamma} b_{\alpha\gamma}(X^{i,N}_t, X^{j,N}_t)\,dt + g_\alpha(t, X^{i,N}_t)\,dW^i_t + \sum_{\gamma=1}^P \frac1{N_\gamma}\sum_{j\in\gamma}\beta_{\alpha\gamma}(X^{i,N}_t, X^{j,N}_t)\,dB^{i\gamma}_t,$$

with independent Brownian motions: intrinsic dynamics $f_\alpha$ with noise $g_\alpha$ (noisy input current or channel noise), and synaptic interactions $b_{\alpha\gamma}$ with noisy synaptic weights $\beta_{\alpha\gamma}$. Initial conditions are i.i.d. within each population.

**Assumptions.** $f_\alpha, g_\alpha$ are locally Lipschitz; $b_{\alpha\gamma}, \beta_{\alpha\gamma}$ are globally Lipschitz and bounded (or of linear growth); and the monotone growth condition $x^\top f_\alpha(t,x) + \tfrac12\|g_\alpha(t,x)\|^2 \le K(1 + \|x\|^2)$ holds. These cover the cubic nonlinearity of FitzHugh–Nagumo and the Hodgkin–Huxley vector field, which are not globally Lipschitz.

**Theorem.**
1. *Mean-field equation.* For every $T > 0$ the McKean–Vlasov system

$$d\bar X^\alpha_t = f_\alpha(t,\bar X^\alpha_t)\,dt + \sum_\gamma \Big(\int b_{\alpha\gamma}(\bar X^\alpha_t, z)\,m^\gamma_t(dz)\Big)dt + g_\alpha(t,\bar X^\alpha_t)\,dW^\alpha_t + \sum_\gamma\Big(\int\beta_{\alpha\gamma}(\bar X^\alpha_t, z)\,m^\gamma_t(dz)\Big)dB^{\alpha\gamma}_t,$$

where $m^\gamma_t$ is the law of $\bar X^\gamma_t$, has a unique solution on $[0,T]$ with $\sup_{t\le T}E\|\bar X_t\|^2 < \infty$.
2. *Convergence.* As all $N_\gamma \to \infty$, the law of each $X^{i,N}$, $i\in\alpha$, converges to the law of $\bar X^\alpha$.
3. *Propagation of chaos.* For every fixed $k$ and neurons $i_1,\dots,i_k$, the joint law of $(X^{i_1,N},\dots,X^{i_k,N})$ converges to the product $\bar m^{\alpha_1}\otimes\cdots\otimes\bar m^{\alpha_k}$ of the corresponding mean-field laws: finitely many neurons become asymptotically independent.

## Proof sketch

Existence and uniqueness of the mean-field equation follow from a Picard iteration in the space of laws on path space: the monotone growth condition gives uniform second-moment bounds that replace global Lipschitz continuity of $f_\alpha$, and local Lipschitz continuity with a stopping-time localization makes the fixed-point map a contraction on bounded sets. For the limit, couple each network neuron with an independent copy of the mean-field process driven by the same Brownian motions (Sznitman's coupling); the difference is controlled by the fluctuation of empirical averages $\frac1{N_\gamma}\sum_j b(x, X^j)$ around $\int b(x,z)\,m(dz)$, which is $O(N_\gamma^{-1/2})$ by independence of the coupled copies. A later clarification by Bossy, Faugeras and Talay (2015) refined parts of the argument for the noisy-synapse terms.

## Sources

- Javier Baladron, Diego Fasoli, Olivier Faugeras and Jonathan Touboul, "Mean-field description and propagation of chaos in networks of Hodgkin-Huxley and FitzHugh-Nagumo neurons", *The Journal of Mathematical Neuroscience* 2 (2012), 10, <https://doi.org/10.1186/2190-8567-2-10>. Preprint version: arXiv:1110.4294 (2011), network and mean-field equations, assumptions, existence–uniqueness theorem and the convergence and propagation-of-chaos theorem, <https://doi.org/10.48550/arXiv.1110.4294>.
