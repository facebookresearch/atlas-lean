# Synaptic balancing on the task-preserving manifold

**Model.** A recurrent rate network of $N$ neurons evolves as

$$\tau\dot x=-x+J\phi(x)+W_{\mathrm{in}}u(t),\qquad y=W_{\mathrm{out}}x,\qquad x(0)=0,$$

with weight configuration $W=(W_{\mathrm{in}},J,W_{\mathrm{out}})$ and a positively homogeneous activation, $\phi(\alpha x)=\alpha\phi(x)$ for all $\alpha>0$ (linear or rectified linear units). For $h\in\mathbb R^N$ and $H=\mathrm{diag}(h)$ define

$$\pi_h(W)=\big(e^{-H}W_{\mathrm{in}},\ e^{-H}Je^{H},\ W_{\mathrm{out}}e^{H}\big),$$

which rescales each existing synapse $J_{ij}\mapsto e^{h_j-h_i}J_{ij}$ by a positive factor and preserves signs, the wiring diagram and the spectrum of $J$.

**Proposition 1 (task preservation).** For every input $u$ and every $h$, the networks with weights $W$ and $\pi_h(W)$ produce the same output trajectory $y(t)$; their hidden states are related by $\tilde x=e^{-H}x$.

**Synaptic costs.** Let $c_{ij}=\alpha_{ij}|J_{ij}|^p$ with $\alpha_{ij}\ge0$, $p>0$ (for robustness to activity noise, $p=2$ and $\alpha_{ij}$ is a variance of the neuronal gain). On the task-preserving manifold $c_{ij}=c^0_{ij}e^{p(h_j-h_i)}$, so the total cost $C(h)=\sum_{ij}c_{ij}$ is convex in $h$ (Proposition 2), and

$$\frac{\partial C}{\partial h_k}=p\Big(\sum_i c_{ik}-\sum_j c_{kj}\Big).$$

*Synaptic balancing* is the gradient flow $\dot h_k=-\big(\sum_i c_{ik}-\sum_j c_{kj}\big)$, a local rule: each neuron compares the total cost of its incoming and outgoing synapses and rescales them reciprocally.

**Balance condition.** A configuration minimizes $C$ on the task-preserving manifold iff, for every neuron $k$,

$$\sum_i c_{ik}=\sum_j c_{kj}.$$

**Proposition 3 (convergence).** If the initial cost matrix $(c^0_{ij})$ is strongly connected, synaptic balancing started from $h=0$ converges exponentially to the unique balanced configuration with $\mathbf 1^{\top}h=0$, which is globally exponentially stable on the task-preserving manifold. **Proposition 4:** every local minimum of a task loss regularized by $\sum_{ij}\alpha_{ij}|J_{ij}|^p$ already satisfies the balance condition.

## Expansion

Proposition 1: substituting $\tilde x=e^{-H}x$ and using $\phi(e^{-H}x)=e^{-H}\phi(x)$ componentwise, $\tau\dot{\tilde x}=-\tilde x+e^{-H}Je^{H}e^{-H}\phi(x)+e^{-H}W_{\mathrm{in}}u$, and the output $W_{\mathrm{out}}e^{H}\tilde x=W_{\mathrm{out}}x$ is unchanged. The cost depends on $h$ only through differences $h_j-h_i$, so $\mathbf 1^{\top}\dot h=0$ and the flow stays on $\mathbf 1^{\top}h=0$. Since the flow does not increase $C$, each $c_{ij}\le C(0)$; along every directed edge with $c^0_{ij}>0$ this bounds $h_j-h_i$, and strong connectivity chains these bounds to confine $h$ to a compact set, where strict convexity in the directions orthogonal to $\mathbf 1$ gives a unique minimizer and exponential convergence. The balanced matrix is the classical diagonal-similarity balancing of a nonnegative matrix.

## Sources

- Stock CH, Harvey SE, Ocko SA, Ganguli S, "Synaptic balancing: A biologically plausible local learning rule that provably increases neural network noise robustness without sacrificing task performance", PLoS Comput Biol (2022), Equations (1)-(5), (10)-(23) and Propositions 1-4, <https://doi.org/10.1371/journal.pcbi.1010418>, PMCID PMC9522011.
