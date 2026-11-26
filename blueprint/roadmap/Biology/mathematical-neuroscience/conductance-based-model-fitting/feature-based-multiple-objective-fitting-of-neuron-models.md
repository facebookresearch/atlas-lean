# Feature-based multiple objective fitting of neuron models

**Feature-based errors.** For a stimulus (e.g. a depolarizing current step) and a feature $\Phi_j$ of the voltage response, let $\bar\Phi_j$ and $\sigma_j$ be the mean and standard deviation of $\Phi_j$ over repeated experimental recordings. For a model with parameters $x$ (maximal conductances), the error of feature $j$ is

$$f_j(x) = \frac{\big|\Phi_j(\text{model}(x)) - \bar\Phi_j\big|}{\sigma_j},$$

the deviation from the experimental mean in units of experimental variability; $f_j = 0$ for all $j$ is a full match to average behavior.

**Example features.** Spike rate (number of spikes divided by the step duration), accommodation index

$$A = \frac{1}{N - k - 1}\sum_{i=k}^{N} \frac{\mathrm{isi}_i - \mathrm{isi}_{i-1}}{\mathrm{isi}_i + \mathrm{isi}_{i-1}} \qquad \text{(Eq. 3)},$$

with $N$ the number of action potentials, $\mathrm{isi}_i$ the inter-spike intervals and $k$ initial intervals discarded as transient; latency to first spike; average spike overshoot; average after-hyperpolarization depth; average spike width.

**Pareto dominance.** For $M$ objectives $f_1, \dots, f_M$, a parameter set $x_1$ dominates $x_2$ iff

$$f_j(x_1) \le f_j(x_2)\ \text{for all } j = 1, \dots, M \qquad \text{(Eq. 1)}, \qquad f_k(x_1) < f_k(x_2)\ \text{for at least one } k \qquad \text{(Eq. 2)}.$$

Dominance is a strict partial order; two solutions are non-dominated when each is better in some objective. The goal is the Pareto front, the set of non-dominated solutions, which displays the optimal trade-offs between features.

**Search.** An elitist non-dominated sorting genetic algorithm (NSGA-II) with real-valued parameters and time-diminishing non-uniform mutation approximates the front; selecting final solutions with error below $2$ standard deviations in every feature yields many distinct models that each reproduce the experimental firing class.

## Expansion

Comparing whole voltage traces point by point penalizes small spike-time shifts as heavily as qualitative failures and ignores trial-to-trial variability. Measuring each feature against its experimental distribution makes the errors dimensionless and comparable, and keeping them as separate objectives avoids choosing arbitrary weights for a single summed cost. Pareto dominance is irreflexive and transitive: if $x_1$ dominates $x_2$ and $x_2$ dominates $x_3$, the non-strict inequalities chain and the strict one is preserved. The source applies the method to the accommodating and fast-spiking classes of cortical interneurons, with six features per class, and obtains hundreds of parameter sets with error below $2$ standard deviations in every feature, spread over broad ranges of several conductances, all matching the recorded firing class.

## Sources

- S. Druckmann, Y. Banitt, A. Gidon, F. Schürmann, H. Markram, I. Segev, "A novel multiple objective optimization framework for constraining conductance-based neuron models by experimental data", Frontiers in Neuroscience 1 (2007), Methods (Eqs. 1–3, "Feature-based error functions"), <https://doi.org/10.3389/neuro.01.1.1.001.2007> (PMC2570085).
