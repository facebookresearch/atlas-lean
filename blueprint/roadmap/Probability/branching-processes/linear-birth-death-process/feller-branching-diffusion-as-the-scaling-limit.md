# Feller's branching diffusion as the scaling limit of critical binary branching

Fix $\gamma>0$ and $x\ge0$, and let $M^N=Z^N/N$ be the rescaled [critical binary branching process](compact-containment-and-c-tightness-for-critical.md), with per-individual birth and death rates $\gamma N/2$ and $Z^N_0=\lfloor Nx\rfloor$. Then for every $T>0$, $M^N$ converges in distribution in $D([0,T],[0,\infty))$ to Feller's branching diffusion started at $x$: the unique law of a continuous process $X$ on $[0,\infty)$ with $X_0=x$ such that

$$f(X_t)-f(X_0)-\int_0^t\frac\gamma2\,X_s\,f''(X_s)\,ds$$

is a martingale for every $f\in C_c^2(\mathbb R)$. This law is that of the unique solution of $dX_t=\sqrt{\gamma X_t^+}\,dB_t$, $X_0=x$, which is absorbed at $0$.

The argument has four steps. The sequence is C-tight by [compact containment and C-tightness](compact-containment-and-c-tightness-for-critical.md). Every limit point solves the martingale problem, by [martingale-problem limits on a locally compact state space](../../markov-chains/martingale-problems/martingale-problem-limits-on-a-locally-compact-s.md), because the generators $A_Nf(z)=\frac{\gamma N^2z}2\bigl[f(z+\frac1N)+f(z-\frac1N)-2f(z)\bigr]$ converge to $\frac\gamma2zf''(z)$ uniformly on the grid and are bounded uniformly in $N$ for $f\in C_c^2$. Every solution of the martingale problem is a weak solution of the SDE, by the [weak SDE representation](../../stochastic-calculus/stochastic-differential-equations/weak-sde-representation-of-one-dimensional-marti.md). The coefficient $\sqrt{\gamma x^+}$ satisfies $|\sqrt{\gamma x^+}-\sqrt{\gamma y^+}|\le\sqrt{\gamma|x-y|}$, so [Yamada–Watanabe pathwise uniqueness](../../stochastic-calculus/stochastic-differential-equations/yamada-watanabe-pathwise-uniqueness-holder-1-2-d.md) holds with $h(u)=\sqrt{\gamma u}$, and the [Yamada–Watanabe theorem](../../stochastic-calculus/stochastic-differential-equations/yamada-watanabe-theorem-weak-existence-pathwise.md) gives uniqueness in law. Hence the martingale-problem law is unique and the whole sequence converges. Discrete-generation Galton–Watson scaling limits are a separate statement.

## Depends on

- [Compact containment and C-tightness for rescaled critical binary branching](compact-containment-and-c-tightness-for-critical.md)
- [Martingale-problem limits on a locally compact state space](../../markov-chains/martingale-problems/martingale-problem-limits-on-a-locally-compact-s.md)
- [Weak SDE representation of one-dimensional martingale-problem solutions](../../stochastic-calculus/stochastic-differential-equations/weak-sde-representation-of-one-dimensional-marti.md)
- [Yamada–Watanabe pathwise uniqueness](../../stochastic-calculus/stochastic-differential-equations/yamada-watanabe-pathwise-uniqueness-holder-1-2-d.md)
- [Yamada–Watanabe theorem](../../stochastic-calculus/stochastic-differential-equations/yamada-watanabe-theorem-weak-existence-pathwise.md)

## Expansion

A full proof checks each hypothesis of the limit theorem for this sequence, including a countable core of test functions in $C_c^2$. The state space $[0,\infty)$ is not compact, so the proof uses localization or the one-point compactification, and the weak SDE representation is applied on the open-ended interval with test functions in $C_c^2(\mathbb R)$. Absorption at $0$ follows from pathwise uniqueness, since $X\equiv0$ solves the SDE from $0$ and the solution can be restarted at the hitting time of $0$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, branching process limits (topic).
- W. Feller, *Diffusion processes in genetics* (1951), as described in E. Baake and A. Wakolbinger, *Feller's contributions to mathematical biology* (2015), <https://arxiv.org/abs/1501.05278>, Feller's branching diffusion as described in the review (background).
