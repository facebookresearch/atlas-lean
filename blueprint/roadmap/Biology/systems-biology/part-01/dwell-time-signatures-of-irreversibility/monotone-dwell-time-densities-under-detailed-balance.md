# Monotone dwell-time densities under detailed balance

**Setting.** Let $X_t$ be an irreducible continuous-time Markov chain on a finite state space with rates $w_{ij}$ ($i \to j$) and stationary law $\pi$. Coarse-grain the microstates into observable mesostates and let $A$ be one mesostate (for example the transcriptionally active state ON) with complement $A^c$. In stationarity, a sojourn in $A$ begins by a jump from $A^c$ into $A$; its length $\tau$ has survival function $P(\tau > t)$ and density $f(t) = -\frac{d}{dt}P(\tau > t)$.

**Theorem (monotone dwell times at equilibrium).** If the chain satisfies detailed balance, $\pi_i w_{ij} = \pi_j w_{ji}$ for all $i, j$, then

$$f(t) = \sum_{k} c_k\, e^{-\mu_k t}, \qquad c_k \ge 0,\ \mu_k > 0 ,$$

so $f$ is completely monotone: in particular $f$ is non-increasing and attains its maximum at $t = 0$. Equivalently, a dwell-time density that is peaked (non-monotone, $f(0) < \sup_t f(t)$), or a survival curve that is sigmoidal, rules out detailed balance: the underlying process produces entropy (dissipates free energy). Monotonicity of the dwell-time density is therefore an equilibrium bound (a Hopfield barrier) that can be crossed only away from equilibrium.

**Special case.** If $A$ is a single microstate (for example the two-state random telegraph model of transcription), $\tau$ is exponential with rate equal to the total exit rate, whether or not detailed balance holds.

## Expansion

Let $Q_{AA}$ be the generator restricted to $A$ (diagonal entries minus total exit rates) and $e_i = \sum_{j \in A^c} w_{ij}$ the exit rate from $i \in A$ into $A^c$. The entry distribution into $A$ is proportional to $\sum_{j \in A^c}\pi_j w_{ji}$, which under detailed balance equals $\pi_i e_i$. Hence, with $\Pi = \mathrm{diag}(\pi_i)_{i \in A}$ and normalizer $Z = \sum_{i \in A}\pi_i e_i$,

$$f(t) = \frac{1}{Z}\, e^\top \Pi\, e^{Q_{AA} t}\, e .$$

Detailed balance makes $\Pi Q_{AA}$ symmetric, so $S = \Pi^{1/2} Q_{AA} \Pi^{-1/2}$ is symmetric with eigenvalues $-\mu_k < 0$ (negative definite because the chain leaves $A$ almost surely) and orthonormal eigenvectors $v_k$. Then $f(t) = Z^{-1}(\Pi^{1/2}e)^\top e^{St}(\Pi^{1/2}e) = Z^{-1}\sum_k (v_k^\top \Pi^{1/2} e)^2 e^{-\mu_k t}$, a nonnegative mixture of exponentials. Without detailed balance the restricted generator can have complex or non-normal spectral structure and the mixture weights can be negative, so $f$ can rise from $f(0)$ to a peak. In single-gene imaging of yeast PHO5 transcription, ON-period survival curves were sigmoidal (best biexponential fit with $f(0) = 0$), indicating an irreversible regulatory process; deleting part of the activation domain of the activator Pho4 made the densities monotone or weakly peaked.

## Sources

- R. Shelansky, S. Abrahamsson, C. R. Brown, M. Doody, T. L. Lenstra, D. R. Larson, H. Boeger, "Single gene analysis in yeast suggests nonequilibrium regulatory dynamics for transcription", Nature Communications 15 (2024), 6226, Results ("Dwell-time density functions are peaked", "The observed process is irreversible", Figs. 2–3) and Supplementary Information (Corollary 1, Theorem 4), <https://doi.org/10.1038/s41467-024-50419-5> (PMC11266658).
- Y. Tu, "The nonequilibrium mechanism for ultrasensitivity in a biological switch: sensing by Maxwell's demons", Proceedings of the National Academy of Sciences USA 105 (2008), 11737–11741, <https://doi.org/10.1073/pnas.0804641105>.
