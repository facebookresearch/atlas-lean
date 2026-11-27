# Non-Markovian interspike intervals of an inhibitory binding neuron with delayed feedback

**Binding neuron.** Identical excitatory input impulses arrive as a Poisson stream of intensity $\lambda$ (the superposition of all input lines). Each impulse is stored in the neuron for a fixed time $\tau$ and then lost (abrupt leakage); the neuron fires as soon as the number of stored impulses reaches the threshold $N_0$, after which its memory is cleared. The analysis takes $N_0 = 2$.

**Inhibitory delayed feedback.** Each output spike enters a feedback line (an autapse) of delay $\Delta$ if the line is empty, and is ignored if the line already carries an impulse, so the line holds at most one impulse. When the fed-back impulse reaches the neuron it annihilates all stored excitatory impulses (fast, shunting inhibition) and has no effect if the memory is empty. The state of the line at the start of an interspike interval is the remaining travel time $s \in (0, \Delta]$ of its impulse; the line is never empty at the start of an interval.

A stationary ISI sequence $(t_j)$ is a Markov chain of order $n$ if $P(t_m \mid t_{m-1},\dots,t_0) = P(t_m \mid t_{m-1},\dots,t_{m-n})$ for all $m > n$, and this fails for every $n' < n$.

**Theorem.** The stationary output stream of interspike intervals (ISIs) of the inhibitory binding neuron with delayed feedback under Poisson stimulation cannot be represented as a Markov chain of any finite order: for every finite $n$, the conditional density $P(t_{n+1} \mid t_n, \dots, t_1, t_0)$ depends on $t_0$.

## Proof sketch

The stream of pairs $(t_k, s_k)$, ISI together with the line's time to live at the start of the interval, is a first-order Markov chain (a lemma of the paper), but the experimentally visible ISIs are a projection of it, because the line state is hidden. Integrating out the hidden $s_k$ gives exact expressions for the joint ISI densities; the conditional density $P(t_{n+1} \mid t_n, \dots, t_0)$ has jump discontinuities whose locations depend on the whole past through the possible arrival times of the hidden inhibitory impulse, including on $t_0$, for every $n$. Numerical simulation confirms the same non-Markov behaviour for higher thresholds.

## Sources

- K.G. Kravchuk and A.K. Vidybida, "Firing statistics of inhibitory neuron with delayed feedback. II: Non-Markovian behavior", *Biosystems* 112 (2013), 233–248, <https://doi.org/10.1016/j.biosystems.2013.02.002>. Preprint version: arXiv:1210.3229 (2012), sections on the binding neuron model, feedback line action and statement of the problem, and the main theorem with its proof outline, <https://doi.org/10.48550/arXiv.1210.3229>.
