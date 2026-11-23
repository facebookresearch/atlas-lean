# Simple-regulation target after an OFF step

Let $\alpha_z, \beta_z, K_{xz}, z_0 \in \mathbb{R}$. The simple-regulation target after the input signal
is removed at time $0$, starting from $Z(0) = z_0$, is the [relaxation solution](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/relaxation.md) $z(t) = z_0 e^{-\alpha t} + \int_0^t e^{-\alpha(t - s)} P(s)\, ds$ with $\alpha = \alpha_z$ and
constant production rate $P$ equal to the [single-input rate](simple-gate.md) with threshold $K_{xz}$
and maximal rate $\beta_z$ at the input $0$.
