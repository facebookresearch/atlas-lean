# Single-cue error-correction learning and zero-discount TD(0)

For a fixed target $\lambda$ and a real gain $\alpha$, the error-correction rule $v_{n+1} = v_n + \alpha(\lambda - v_n)$ has the closed form $v_n - \lambda = (1 - \alpha)^n(v_0 - \lambda)$. If $v_0 \ne \lambda$, then $v_n \to \lambda$ exactly when $0 < \alpha < 2$; the approach is monotone, without oscillation, exactly when $0 < \alpha \le 1$ ($\alpha = 1$ reaches $\lambda$ in one step), and $\alpha = 0$ leaves $v_n = v_0$. The tabular TD(0) update $V(s) \leftarrow V(s) + \alpha(r + \gamma V(s') - V(s))$ with discount $\gamma = 0$, applied repeatedly to one state whose reward is always $\lambda$, is this rule with $v_n$ the current value of that state. This is a deterministic single-cue model; stochastic TD convergence and multi-cue conditioning are not covered.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Closed form and convergence of the scalar affine recurrence $x_{n+1} = ax_n + b$.

## Sources

- R. S. Sutton and A. G. Barto, *Reinforcement Learning: An Introduction*, 2nd ed., MIT Press, 2018, <http://incompleteideas.net/book/RLbook2020.pdf>, §6.1, equation (6.2)
