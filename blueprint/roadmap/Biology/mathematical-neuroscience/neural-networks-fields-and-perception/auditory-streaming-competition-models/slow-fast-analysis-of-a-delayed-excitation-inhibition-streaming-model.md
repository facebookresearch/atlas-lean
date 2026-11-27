# Slow–fast analysis of a delayed excitation–inhibition streaming model

**Model.** Two populations with firing rates $u_A, u_B$ and inhibitory synaptic variables $s_A, s_B$ obey the delay differential equations

$$\tau\dot u_A = -u_A + H\big(a u_B - b s_B(t - D) + i_A(t)\big), \qquad \tau\dot u_B = -u_B + H\big(a u_A - b s_A(t - D) + i_B(t)\big),$$

$$\dot s_X = H(u_X)(1 - s_X)/\tau - s_X/\tau_i, \qquad X \in \{A, B\},$$

where $H(x) = \mathbf 1[x \ge \theta]$ with threshold $\theta \in (0,1)$, $a \ge 0$ is the fast excitation strength, $b \ge 0$ the strength of inhibition with delay $D$ and slow decay time $\tau_i \gg \tau$. Tones are presented alternately: A tones on $I_A^k = [2kT_R, 2kT_R + T_D]$ and B tones on $I_B^k = [(2k+1)T_R, (2k+1)T_R + T_D]$, with $T_R \ge T_D$ and $T_R \ge D$, and

$$i_A = c\sum_k \chi_{I_A^k} + d\sum_k \chi_{I_B^k}, \qquad i_B = d\sum_k \chi_{I_A^k} + c\sum_k \chi_{I_B^k}, \qquad c \ge d \ge 0.$$

Let $I$ be the union of all tone intervals. Assume (U1) $a - b < \theta$ and (U2) $c \ge \theta$.

**Theorem.** In the singular limit $\tau \to 0$:
1. Without input, (U1) makes the quiescent state $(0,0,0,0)$ the only equilibrium; if instead $a - b \ge \theta$, the active state $(1,1,1,1)$ coexists and every trajectory with $c \ge \theta$ ends there.
2. (Dynamics between tones) For $t \notin I$: if either unit is OFF at $t$, both units are OFF from $t$ until the next tone onset; if either unit is ON at $t$, both have been ON since the end of the preceding tone interval. Hence each unit can switch ON only during a tone, and every state is either *LONG* (both units ON at some time between tones) or *SHORT* (both OFF between all tones).
3. If $T_D + D < T_R$, both units are OFF at the start of each tone interval and each unit switches ON at most once per tone interval; the periodic states are then classified by binary matrices recording which unit switches on in each interval, with explicit inequalities in $(a, b, c, d, \theta, \tau_i, D, T_D, T_R)$ for their existence.

These states map onto percepts: responses of both units to every tone correspond to integration, responses of each unit only to its own tone to segregation, with slow delayed inhibition masking the subsequent tone during segregation and fast excitation allowing integration even for large pitch differences.

## Expansion

With $\tau \to 0$ the rates are slaved to the quasi-equilibria of the fast subsystem, which for a Heaviside gain take values in $\{0,1\}^2$ and depend on the delayed synaptic values $\tilde s_X = s_X(t-D)$ through threshold inequalities; between tones ($c = d = 0$) only $(0,0)$ and, when $a - b\tilde s_A \ge \theta$ and $a - b\tilde s_B \ge \theta$, $(1,1)$ exist, which gives part 2. The synaptic variables then evolve by explicit exponentials, rising toward $1$ at rate $1/\tau + 1/\tau_i$ while their unit is ON and decaying at rate $1/\tau_i$ while it is OFF, so the switching times solve scalar equations in these exponentials. Under $T_D + D < T_R$ the inhibition felt during a tone comes from activity that ended before it, so the delayed synaptic input is monotonically decreasing over the first $D$ of each tone, which yields the single switch per interval and the finite binary bookkeeping of part 3. A smooth sigmoid gain reproduces the same states numerically.

## Sources

- A. Ferrario, J. Rankin, "Auditory streaming emerges from fast excitation and slow delayed inhibition", Journal of Mathematical Neuroscience 11 (2021) 8, Eqs. (1)–(2), Remark 2.1, Theorem 1, Definitions 5.1 and 6.2–6.4, and Lemmas 3–5, <https://doi.org/10.1186/s13408-021-00106-2>, PMCID PMC8093365.
