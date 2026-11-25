# Finite-state rare-transition limit for the last-visited absorbing state (Schur-complement form)

Let $\mathcal X=R\sqcup T$ be a finite state space with $R$ nonempty. Let $Q_0$ be a rate matrix (nonnegative off-diagonal entries, zero row sums) whose rows indexed by $R$ vanish, so every state of $R$ is absorbing, and such that from every $y\in T$ the chain with generator $Q_0$ is absorbed in $R$ almost surely. Then $-Q_{0,TT}$ is nonsingular and $A=(-Q_{0,TT})^{-1}Q_{0,TR}$ is the matrix of absorption probabilities $a(y,h)$, $y\in T$, $h\in R$. Let $Q_1$ be a real matrix with zero row sums, not necessarily a rate matrix (entries in rows of $T$ may be negative), and $\varepsilon_1>0$ such that $Q_\varepsilon=Q_0+\varepsilon Q_1$ is a rate matrix for $0<\varepsilon\le\varepsilon_1$. $Q_1$ may act on rows of $R$ (rare exits, including direct jumps within $R$) and on rows of $T$.

(a) There is $\varepsilon_0\in(0,\varepsilon_1]$ such that $-Q_{\varepsilon,TT}$ is nonsingular for $0<\varepsilon\le\varepsilon_0$. For such $\varepsilon$, the trace on $R$ of the chain with generator $Q_\varepsilon$ (the chain time-changed by its occupation time of $R$) is a continuous-time Markov chain with the Schur-complement generator

$$S_\varepsilon=Q_{\varepsilon,RR}+Q_{\varepsilon,RT}(-Q_{\varepsilon,TT})^{-1}Q_{\varepsilon,TR}.$$

(b) Since $Q_{0,RR}=0$ and $Q_{0,RT}=0$,

$$\frac{S_\varepsilon}{\varepsilon}=Q_{1,RR}+Q_{1,RT}(-Q_{0,TT}-\varepsilon Q_{1,TT})^{-1}(Q_{0,TR}+\varepsilon Q_{1,TR})\longrightarrow\bar q:=Q_{1,RR}+Q_{1,RT}A\qquad(\varepsilon\to0^+),$$

that is, $\bar q(g,h)=Q_1(g,h)+\sum_{y\in T}Q_1(g,y)\,a(y,h)$ for $h\ne g$, with diagonal minus the off-diagonal row sum. The perturbations $Q_{1,TT}$ and $Q_{1,TR}$ of the fast dynamics change $S_\varepsilon/\varepsilon$ only by $O(\varepsilon)$. If $T=\emptyset$, then $\bar q=Q_{1,RR}$.

(c) Fix an initial state $g_0\in R$. Let $L_t$ be the last state of $R$ visited by the $Q_\varepsilon$-chain up to time $t$. As $\varepsilon\to0^+$, the finite-dimensional distributions of $(L_{t/\varepsilon})_{t\ge0}$ and of the trace process at trace time $t/\varepsilon$ converge to those of the continuous-time Markov chain on $R$ with generator $\bar q$ started at $g_0$.

The neighbourhood in (a) is needed: for $Q_0=\begin{pmatrix}0&0\\1&-1\end{pmatrix}$, $Q_1=\begin{pmatrix}-1&1\\-1&1\end{pmatrix}$, $R=\{1\}$, $T=\{2\}$ and $\varepsilon_1=1$, every $Q_\varepsilon$ is a rate matrix, but $Q_{1,TT}=-Q_{0,TT}$ makes the transient block singular at $\varepsilon=1$.

## Depends on

- [Path of a continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
- [Backward equations for the mean hitting time](../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/ctmc-hitting-time-backward.md)

## Proof depends on

- [Transition function of a rate matrix is stochastic](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition-mem-row-stochastic.md)

## Expansion

A proof page must establish:

- existence of $\varepsilon_0$ by continuity of matrix inversion at $-Q_{0,TT}$, and the Schur-complement formula (a) for every $0<\varepsilon\le\varepsilon_0$, the endpoint of the guard example being outside its range;
- the limit (b), with the $O(\varepsilon)$ bound on the transient-row terms, and the case $T=\emptyset$;
- for (c), a bound on the expected time spent in $T$ per excursion, uniform for small $\varepsilon$ (row sums of $(-Q_{\varepsilon,TT})^{-1}$ converge to those of $(-Q_{0,TT})^{-1}$), and tightness of the number of excursions up to time $t/\varepsilon$, so that real time and trace time differ by $o(1/\varepsilon)$ in probability;
- convergence of the trace chains with generators $S_\varepsilon/\varepsilon$ to the chain with generator $\bar q$ from convergence of the generators on a finite state space.

The related discrete-time result for two time scales is [Möhle's lemma](../../../Probability/markov-chains/finite-markov-chains/mohle-s-separation-of-timescales-lemma-for-finit.md).

## Sources

- N. Champagnat, *A microscopic interpretation for adaptive dynamics trait substitution sequence models*, Stochastic Processes and their Applications 116 (2006), 1127–1160, <https://ideas.repec.org/a/eee/spapps/v116y2006i8p1127-1160.html> (separation of time scales; motivation only). The finite-state statement above is a local derivation.
