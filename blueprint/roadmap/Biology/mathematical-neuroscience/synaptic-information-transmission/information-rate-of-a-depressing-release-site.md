# Information rate of a depressing synaptic release site

**Model (binary asymmetric channel with a memory of release outcomes).** Time is discrete. The input $X = (X_i)$ is an i.i.d. Bernoulli spike train with $P(X_i = 1) = \alpha \in (0,1)$, and $\bar\alpha = 1 - \alpha$. The output $Y_i \in \{0,1\}$ records whether the release site releases a vesicle at time $i$. Given the last $L \ge 1$ release outcomes, the site is in state

$$j = Y_{i-1} + 2Y_{i-2} + \dots + 2^{L-1} Y_{i-L}, \qquad 0 \le j \le 2^L - 1,$$

and releases with synchronous probability $p(j) = P(Y_i = 1 \mid X_i = 1, j)$ and asynchronous probability $q(j) = P(Y_i = 1 \mid X_i = 0, j)$, with $p(j), q(j) \in (0,1)$. Short-term depression is encoded by $p(j), q(j)$ decreasing after releases and recovering toward defaults $p_0, q_0$ in quiescent intervals. The states form an ergodic Markov chain on $2^L$ states with stationary distribution $(\pi_j)$.

Let $h(x) = -x \log_2 x - (1-x)\log_2(1-x)$ and define the per-state rate

$$R_j = h\big(\bar\alpha\, q(j) + \alpha\, p(j)\big) - \bar\alpha\, h(q(j)) - \alpha\, h(p(j)).$$

**Theorem 1.** The mutual information rate between input spikes and release outcomes is

$$R_D = \sum_{j=0}^{2^L - 1} R_j\, \pi_j .$$

**Theorem 2.** If each release costs one unit of energy, the energy-normalized information rate is

$$R_D^{(E)} = \frac{\sum_{j=0}^{2^L-1} R_j \pi_j}{\sum_{j=0}^{2^{L-1}-1} \pi_{2j+1}},$$

the denominator being the stationary release probability (states with $Y_{i-1} = 1$).

**Corollary (no depression).** With constant $p_0, q_0$,

$$R_0 = h(\bar\alpha q_0 + \alpha p_0) - \bar\alpha h(q_0) - \alpha h(p_0), \qquad R_0^{(E)} = \frac{R_0}{\bar\alpha q_0 + \alpha p_0}.$$

## Expansion

Conditioned on the state, the release site at time $i$ is a memoryless binary asymmetric channel with crossover probabilities $q(j)$ and $1 - p(j)$, whose mutual information with an input of mean $\alpha$ is $R_j$. Because the inputs are i.i.d. and the state is a deterministic function of past outputs, the chain rule for the information rate $\lim_n \frac1n I(X^n; Y^n)$ splits into conditional single-letter terms, and ergodicity of the state chain replaces the time average of $R_{j_i}$ by its stationary mean. Normalizing by the expected number of releases per time step gives Theorem 2. The consequence emphasized by the model is that depression can raise $R_D^{(E)}$ above $R_0^{(E)}$, and, when asynchronous release is substantial, even raise $R_D$ above $R_0$: lowering release probability right after a release mostly removes uninformative asynchronous releases.

## Sources

- M. Salmasi, A. Loebel, S. Glasauer, M. Stemmler, "Short-term synaptic depression can increase the rate of information transfer at a release site", PLoS Computational Biology 15(1) (2019) e1006666, Methods, Equations (1)-(7), Theorem 1, Theorem 2 and Corollary 1, <https://doi.org/10.1371/journal.pcbi.1006666>, PMCID PMC6355030.
