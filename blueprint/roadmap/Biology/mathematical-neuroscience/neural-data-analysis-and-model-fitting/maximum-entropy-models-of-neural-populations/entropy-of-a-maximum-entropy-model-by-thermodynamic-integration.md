# Entropy of a maximum entropy model by thermodynamic integration

**Setting.** Let $P(\sigma) = e^{-E(\sigma)}/Z$ be a [maximum entropy model](pairwise-and-k-pairwise-maximum-entropy-models-of-spiking-patterns.md) on the finite state space $\{0,1\}^N$, and let $S = -\sum_\sigma P(\sigma)\log P(\sigma)$ be its entropy (in nats). Direct estimation from samples is infeasible for large $N$, because almost every observed pattern is unique.

**Temperature family.** For $T > 0$ define

$$P_T(\sigma) = \frac{1}{Z(T)}\, e^{-E(\sigma)/T}, \qquad Z(T) = \sum_\sigma e^{-E(\sigma)/T},$$

so $P_1 = P$. Let $U(T) = \langle E \rangle_T$, $S(T)$ the entropy of $P_T$, and

$$C(T) = \frac{dU}{dT} = \frac{\langle E^2 \rangle_T - \langle E \rangle_T^2}{T^2}$$

the heat capacity, i.e. the variance of the energy (of the log-probability, the "surprise") scaled by $T^{-2}$.

**Statement 1 (heat-capacity integral).** $\dfrac{dS}{dT} = \dfrac{C(T)}{T}$, and if the minimum of $E$ is attained at a unique state then $S(T) \to 0$ as $T \to 0^+$, so

$$S = S(1) = \int_0^1 \frac{C(T)}{T}\, dT .$$

Each $C(T)$ can be estimated by Monte Carlo sampling from $P_T$ (energy variance), which stabilizes far sooner than estimates of the probabilities of individual states.

**Statement 2 (entropy from the silent state).** If the all-silent pattern $\mathbf 0$ has energy $E(\mathbf 0)$ and probability $P(\mathbf 0)$, then

$$Z = \frac{e^{-E(\mathbf 0)}}{P(\mathbf 0)}, \qquad S = \log Z + \langle E \rangle .$$

For K-pairwise models $P(\mathbf 0)$ equals the empirical probability of silence (it is one of the matched constraints, $P(K = 0)$), and $E$ can be shifted so that $E(\mathbf 0) = 0$; then $S = -\log P_{\mathrm{data}}(K = 0) + \langle E \rangle$, needing only one Monte Carlo estimate of the mean energy.

## Depends on

- [Pairwise and K-pairwise maximum entropy models of spiking patterns](pairwise-and-k-pairwise-maximum-entropy-models-of-spiking-patterns.md)

## Expansion

With $\beta = 1/T$, $\log P_T = -\beta E - \log Z$, so $S(T) = \beta U + \log Z$. Since $\frac{d}{d\beta}\log Z = -U$, $\frac{dS}{d\beta} = U + \beta\frac{dU}{d\beta} - U = \beta\frac{dU}{d\beta}$, and converting to $T$ gives $\frac{dS}{dT} = \frac1T\frac{dU}{dT}$. Also $\frac{dU}{d\beta} = -\mathrm{Var}_T(E)$, giving $C = \mathrm{Var}_T(E)/T^2$. As $T \to 0^+$, $P_T$ concentrates on the minimizers of $E$, so $S(T) \to \log(\text{number of minimizers})$, which is $0$ for a unique ground state (in the retinal data the most probable state, complete silence). Statement 2 is the definition of $P(\mathbf 0)$ solved for $Z$, combined with $S = \langle -\log P \rangle = \langle E \rangle + \log Z$. Because maximum entropy models reproduce the measured constraints with maximal entropy, $S$ upper-bounds the entropy of the true pattern distribution that shares those statistics, and the difference between the independent-neuron entropy and $S$ (the multi-information) measures the statistical structure captured by the interactions.

## Sources

- G. Tkačik, O. Marre, D. Amodei, E. Schneidman, W. Bialek, M. J. Berry II, "Searching for collective behavior in a large network of sensory neurons", PLoS Computational Biology (2014), Results ("entropy" estimation), Eqs. (28)–(29) (temperature family and heat-capacity integral), Eqs. (30)–(31) (silent-state estimate of $Z$ and entropy) and Eq. (32) (multi-information), <https://doi.org/10.1371/journal.pcbi.1003408> (PMC3879139).
