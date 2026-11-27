# Modularity principle for energy functions of spiking networks

Consider $N$ stochastic spiking neurons. Neuron $k$ fires with instantaneous probability $\frac{1}{\tau}\exp(u_k(t))$ per unit time, its membrane potential is

$$u_k(t) = b_k + \sum_{l} w_{kl}\,x_l(t),$$

and $x_l(t) = 1$ if neuron $l$ spiked within $(t - \tau, t]$ (rectangular postsynaptic potentials of length $\tau$, equal to the refractory period), else $0$. With enough noise the distribution of the network state $\mathbf x(t) \in \{0,1\}^N$ converges to a unique stationary law $p(\mathbf x)$, written $p(\mathbf x) \propto e^{-E(\mathbf x)}$. For symmetric weights $w_{kl} = w_{lk}$, $w_{kk} = 0$, it is the Boltzmann distribution with

$$E_{\mathcal N}(\mathbf x) = -\sum_k b_k x_k - \tfrac12\sum_{k,l} w_{kl}\,x_k x_l .$$

The **neural computability condition** says a network samples from $p$ if each neuron satisfies $u_k(t) = E(x_k = 0, \mathbf x_{\setminus k}(t)) - E(x_k = 1, \mathbf x_{\setminus k}(t))$.

**Theorem (modularity principle).** Let $\mathcal N$ be such a symmetric principal network and $\mathcal C = \{C_1, \dots, C_L\}$ auxiliary circuits, possibly with asymmetric connections, that add contributions $u_{k,i}(t)$ to the membrane potential $u_k(t) = b_k + \sum_l w_{kl}x_l(t) + \sum_i u_{k,i}(t)$ of principal neuron $k$. Suppose that for each $C_i$ there is a function $U_i(\mathbf x)$ of the principal state with

$$u_{k,i}(t) = U_i(x_k = 0, \mathbf x_{\setminus k}(t)) - U_i(x_k = 1, \mathbf x_{\setminus k}(t))$$

for every principal neuron $k$ and every $t$, regardless of which other circuits are present. Then for any subset $\mathcal I$ of circuits the principal network's energy function is

$$E_{\mathcal N, \mathcal I}(\mathbf x) = E_{\mathcal N}(\mathbf x) + \sum_{i \in \mathcal I} U_i(\mathbf x).$$

## Expansion

Membrane integration is linear, so the contributions of the principal weights and of each circuit add; under the hypothesis, the total potential of each principal neuron equals the energy difference of $E_{\mathcal N} + \sum_{i \in \mathcal I} U_i$ for flipping that neuron, which is exactly the neural computability condition for that energy. Auxiliary neurons may relate stochastically to principal neurons, avoiding the large energy barriers that arise when higher-order terms are built from deterministically defined, symmetrically connected hidden units. Examples are a winner-take-all motif, which raises the energy of states in which not exactly one of $K$ principal neurons is active (encoding a $K$-valued variable), and an OR motif with one excitatory and one inhibitory auxiliary neuron that penalizes states with none of its principal neurons active, which together encode traveling-salesman and 3-SAT instances as energy landscapes searched by the network's stochastic dynamics.

## Sources

- Z. Jonke, S. Habenschuss, W. Maass, "Solving constraint satisfaction problems with networks of spiking neurons", Frontiers in Neuroscience 10 (2016) 118, Equations 1–9 and Theorem 1 (Modularity Principle), <https://doi.org/10.3389/fnins.2016.00118>, PMCID PMC4811945.
