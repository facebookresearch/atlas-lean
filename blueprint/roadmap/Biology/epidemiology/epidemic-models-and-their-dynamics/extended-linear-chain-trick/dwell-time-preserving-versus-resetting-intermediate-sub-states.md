# Dwell-time-preserving versus dwell-time-resetting intermediate sub-states in linear chain models

**Setting.** Particles enter a base sub-state $X_0$ of a state X at rate $\mathcal I_X(t)$. Two independent clocks run from entry: $T_0$, a Poisson-process $k_0$-th event time with rate $r_0(t)$ (leaving X), and $T_1$, a Poisson-process $k_1$-th event time with rate $r_1(t)$ (moving to an intermediate sub-state $X_I$ of X, for example quarantine of an infectious individual). A particle leaves $X_0$ at $T = \min(T_0,T_1)$. Track the base sub-state by $x_{0(a,b)}$, $a \in \{1,\dots,k_0\}$, $b \in \{1,\dots,k_1\}$, the amount that has seen $a-1$ events of the first clock and $b-1$ of the second:

$$ \dot x_{0(a,b)} = \mathcal I_X(t)\,\mathbf 1_{a=b=1} + r_0(t)\,x_{0(a-1,b)}\mathbf 1_{a>1} + r_1(t)\,x_{0(a,b-1)}\mathbf 1_{b>1} - \big(r_0(t)+r_1(t)\big)\,x_{0(a,b)}. $$

The flux out of X directly from the base is $r_0(t)\sum_b x_{0(k_0,b)}$, and the flux into $X_I$ from base sub-state $(a,k_1)$ is $r_1(t)\,x_{0(a,k_1)}$.

**Theorem (resetting intermediate state).** If a particle in $X_I$ stays for an independent Poisson-process $\kappa$-th event time with rate $\varrho(t)$, then $X_I$ is a chain of $\kappa$ sub-states

$$ \dot x_{I1} = r_1(t)\sum_{a=1}^{k_0} x_{0(a,k_1)} - \varrho(t)\,x_{I1}, \qquad \dot x_{Ik} = \varrho(t)\,(x_{I,k-1} - x_{Ik}), \quad k = 2,\dots,\kappa, $$

with exit flux $\varrho(t)\,x_{I\kappa}$. The total time in X then depends on whether the transition to $X_I$ occurred.

**Theorem (dwell-time-preserving intermediate state).** Suppose instead that the overall time in X must be the $k_0$-th event time with rate $r_0(t)$ whether or not the particle passes through $X_I$. A particle that enters $X_I$ after $a-1$ of the $k_0$ events must stay for a $(k_0-a+1)$-th event time with rate $r_0(t)$. Then $X_I$ is a chain of $k_0$ sub-states, and particles enter at the position given by the number of events of the first clock already seen:

$$ \dot x_{Ik} = r_1(t)\,x_{0(k,k_1)} + r_0(t)\,x_{I,k-1}\mathbf 1_{k>1} - r_0(t)\,x_{Ik}, \quad k = 1,\dots,k_0, $$

with exit flux $r_0(t)\,x_{Ik_0}$. With these equations, every particle's total time in X has the law of $T_0$, and the intermediate transition only labels part of the time spent there.

## Expansion

Both results come from applying the competing-clocks linear chain trick to $X_0$, which is the minimum of independent event times, so the base sub-states form a $k_0 \times k_1$ grid. In the resetting case $X_I$ is just another recipient state with its own chain. In the preserving case the weak memorylessness of Poisson first event times (given that $a-1$ events have occurred, the remaining time to the $k_0$-th event is a $(k_0-a+1)$-th event time started now) means $X_I$ can reuse the remaining part of the $T_0$ chain. Conditioning on the event count, rather than on the exact elapsed time, keeps the model a finite ODE system. For $k_0 = k_1 = 2$ the preserving model routes $x_{0(1,2)}$ into $x_{I1}$ and $x_{0(2,2)}$ into $x_{I2}$, while the resetting model routes both into $x_{I1}$. This is how one models quarantine that lowers transmission without changing the infectious-period distribution.

## Sources

- Paul J. Hurtado and Adam S. Kirosingh, "Generalizations of the 'Linear Chain Trick': Incorporating more flexible dwell time distributions into mean field ODE models", arXiv:1808.07571 (2018): Section 3, Theorem 6 (competing Poisson processes), Theorem 8 (dwell-time-altering intermediate sub-states), Theorem 9 (dwell-time-preserving intermediate sub-states), Examples 3.7 and 3.8. <https://doi.org/10.48550/arXiv.1808.07571> Published version: Journal of Mathematical Biology. 79, 1831-1883, October 2019, <https://doi.org/10.1007/s00285-019-01412-w>.
