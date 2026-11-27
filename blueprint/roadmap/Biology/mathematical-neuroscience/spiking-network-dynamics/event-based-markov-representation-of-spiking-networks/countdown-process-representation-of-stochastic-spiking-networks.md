# Countdown-process representation of stochastic spiking networks

**Countdown process.** In a network of $N$ spiking neurons, let $X^{(i)}(t) \ge 0$ be the time remaining until neuron $i$ would next fire if it received no spike in the meantime. Between events $\frac{d}{dt}X^{(i)}(t) = -1$ for every $i$, and the next spike is fired by $i^* = \arg\min_j X^{(j)}(t)$ at time $t + X^{(i^*)}(t)$. At that spike:
- the firing neuron's countdown is redrawn from its *reset random variable* $Y^{(i^*)}$ (the time to the next spike from the reset state with no input);
- every neuron $j$ that receives the spike has its countdown replaced according to an *interaction random variable* $\eta_{i^*j}$, whose law depends only on the current countdown value $X^{(j)}$;
- the initial countdowns are drawn from an *initialization random variable* $Y_0$, the vector of first spike times from the initial state with no interactions.
The embedded *countdown sequence* $(X_n, t_n)$ records the countdowns at successive spike times $t_n$.

**Theorem.** Let a network of $N$ spiking neurons with state $V_t$ (membrane potentials and possibly other variables) start from $V_0$, and suppose that the law of $Y_0$, the laws of the one-dimensional reset variables $Y^{(i)}$, and the laws of the one-dimensional interaction variables $\eta_{ij}$ conditional on the last countdown value are known and depend only on the countdown state at the spike time. Then the law of the spike times of the network equals the law of the spike times of the countdown process (equivalently, of the countdown sequence) with these ingredients. Moreover:
1. the continuous-time countdown process and the discrete countdown sequence are in pathwise one-to-one correspondence;
2. the countdown process is a Markov process and the countdown sequence a Markov chain;
3. with time-dependent input or threshold, $(X_n, t_n)$ (with $t_n$ the last spike time) is an autonomous Markov chain;
4. inhibitory networks of perfect integrate-and-fire neurons $\tau_i\,dV^{(i)} = I_e^{(i)}(t)\,dt + \sigma_i\,dW^{(i)}_t$, with jumps $V^{(j)} \mapsto V^{(j)} + w_{ij}$ at incoming spikes, satisfy these hypotheses, with reset and interaction variables given by first-passage times of Brownian motion to explicit moving boundaries; and a network of perfect integrate-and-fire neurons with both excitatory and inhibitory connections also has a Markovian event-based description.

## Proof sketch

Spikes are the only events that couple neurons, so between them each neuron evolves independently and its future is summarized by the time at which it would cross threshold. When a neuron with countdown $X^{(j)}$ receives an inhibitory jump $w_{ij} < 0$, it cannot fire before $X^{(j)}$ and, by the strong Markov property of the noise, the extra delay after $X^{(j)}$ is a fresh first-passage time, independent of the past given $X^{(j)}$. This makes the spike-time dynamics Markov in the countdown variables, which enables exact event-driven simulation of large noisy networks without discretizing the membrane SDEs. For leaky integrate-and-fire and synaptic-current models the same structure holds, with reset and interaction laws given by first-passage times of Ornstein–Uhlenbeck-type processes.

## Sources

- Jonathan D. Touboul and Olivier D. Faugeras, "A Markovian event-based framework for stochastic spiking neural networks", *Journal of Computational Neuroscience* 31 (2011), 485–507, <https://doi.org/10.1007/s10827-011-0327-y>. Preprint version: arXiv:0911.3462 (2009), Section 1 (definition of the countdown process, Proposition 1.1, Theorem 1.2, Proposition 1.3), Section 2 (perfect and leaky integrate-and-fire neurons, Proposition 2.1), Section 3 (excitatory networks, Proposition 3.1), <https://doi.org/10.48550/arXiv.0911.3462>.
