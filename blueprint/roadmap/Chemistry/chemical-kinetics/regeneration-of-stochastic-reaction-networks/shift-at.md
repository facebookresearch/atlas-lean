# Steps after a random time

Let $S$ be a set, consider step sequences $\omega = (\omega_n)_{n \in \mathbb{N}}$ with
$\omega_n = (\xi_n, E_n)$, $\xi_n : S \to S$ and $E_n \in \mathbb{R}$, and let $\tau$ be any
function from step sequences to $\mathbb{N} \cup \{\infty\}$. The steps after $\tau$ form the step
sequence $\theta_\tau \omega$ obtained by the
[shift](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md)
by $\tau(\omega)$ steps: when $\tau(\omega) < \infty$,
$(\theta_\tau \omega)_m = \omega_{\tau(\omega) + m}$ for every $m \in \mathbb{N}$; when
$\tau(\omega) = \infty$, $\theta_\tau \omega = \omega$ is the shift by $0$ steps, since the
conversion from $\mathbb{N} \cup \{\infty\}$ to $\mathbb{N}$ sends $\infty$ to $0$. No stopping-time
property of $\tau$ is assumed.
