# Simple-regulation target after an ON step

Let $\alpha_z, \beta_z, K_{xz} \in \mathbb{R}$. The simple-regulation target after an ON step of the
input signal at time $0$, starting from $Z(0) = 0$, is the [relaxation solution](relaxation.md) $z(t) = z_0 e^{-\alpha t} + \int_0^t e^{-\alpha(t - s)} P(s)\, ds$ with $\alpha = \alpha_z$,
$z_0 = 0$ and constant production rate $P$ equal to the [single-input rate](simple-gate.md) with
threshold $K_{xz}$ and maximal rate $\beta_z$ at the input $1$.
