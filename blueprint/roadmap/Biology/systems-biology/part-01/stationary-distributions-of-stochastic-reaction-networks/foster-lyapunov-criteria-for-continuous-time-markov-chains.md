# Foster–Lyapunov criteria for stationary distributions of continuous-time Markov chains

**Setting.** A stochastic reaction network, or any continuous-time Markov chain, on a countable state space $\mathcal{S}$ has a rate matrix $Q = (q(x,y))$ with $q(x,y) \ge 0$ for $x\ne y$ and $\sum_y q(x,y) = 0$. For $v : \mathcal{S}\to\mathbb{R}$ write $Qv(x) = \sum_y q(x,y)v(y)$. A function $w$ is **norm-like** if every sublevel set $\{x : w(x) < r\}$ is finite. $Q$ is **regular** if the minimal chain does not explode. In that case a distribution $\pi$ is stationary, $\pi P_t = \pi$ for all $t$, if and only if $\pi Q = 0$, the stationary chemical master equation (Miller, 1963).

**Theorem.**

1. *(Regularity)* $Q$ is regular if and only if there are a norm-like $v$ and constants $d_1, d_2 \in \mathbb{R}$ with $Qv \le d_1 v + d_2$ on $\mathcal{S}$.
2. *(Boundedness in probability and moment bounds)* Suppose $Q$ is regular and, for a finite set $F$, a constant $d > 0$ and functions $f \ge 1$, $v \ge 0$,

$$Qv(x) \le d\,\mathbf{1}_F(x) - f(x) \qquad \forall x \in \mathcal{S}.$$

Then the chain is bounded in probability, and every stationary distribution $\pi$ satisfies

$$1 \le \pi(f) \le d\,\pi(F) \le d, \qquad \pi(\mathcal{S}\setminus F) \le 1 - \frac{1}{d}.$$

Conversely, if $Q$ is regular and $\mathcal{S}$ consists of finitely many closed communicating classes with no transient states, then boundedness in probability implies that such $F, d, f, v$ exist.
3. *(Exponential ergodicity)* If $Qv \le -d_1 v + d_2$ for some $d_1 > 0$, $d_2\in\mathbb{R}$ and norm-like $v \ge 1$, then $Q$ is regular, the chain is bounded in probability, and for every initial law $\lambda$ with $\lambda(v) < \infty$ the time-varying law converges exponentially fast to its stationary limit.

**Tail bounds for truncation.** If $\pi(w) \le c$ for a nonnegative norm-like $w$, for example from criterion 2 with $f = w$, then the truncation $\mathcal{S}_r = \{w < r\}$ has tail mass

$$m_r = \sum_{x\notin\mathcal{S}_r}\pi(x) \le \frac{c}{r}.$$

This tail mass equals both the $\ell^1$ and the total-variation distance between $\pi$ and its restriction to $\mathcal{S}_r$. It therefore certifies the error of finite-state-projection and truncation-and-augmentation schemes for the chemical master equation.

## Expansion

Applying Dynkin's formula to $v$ under the drift inequality in criterion 2 and averaging in time gives $\frac{1}{t}\int_0^t \mathbb{E}f(X_s)\,ds \le d\,\frac{1}{t}\int_0^t\Pr(X_s\in F)\,ds + \mathbb{E}v(X_0)/t$. Hence the chain spends a positive fraction of time in the finite set $F$, and stationary averages of $f$ are at most $d\,\pi(F)$. The tail bound is Markov's inequality on the sublevel sets of $w$. For reaction networks with mass-action kinetics, polynomial $v$ such as total molecule number often satisfy these inequalities. The review gives these criteria without irreducibility assumptions and shows the stationary distributions are exactly the convex combinations of the ergodic distributions of the positive recurrent closed classes.

## Sources

- J. Kuntz, P. Thomas, G.-B. Stan and M. Barahona, "Stationary distributions of continuous-time Markov chains: a review of theory and truncation-based approximations", arXiv:1909.05794 (2019), Section 2 (stationary distributions; Foster–Lyapunov stability criteria) and Section 3 (truncation error), <https://doi.org/10.48550/arXiv.1909.05794>.
