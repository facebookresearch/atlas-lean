# The tent map as a composition of ReLUs

For every real $x$, the [tent map](tent.md) satisfies $\mathrm{tent}(x) = \mathrm{relu}(2\,\mathrm{relu}(x) - 4\,\mathrm{relu}(x - 1/2))$, where $\mathrm{relu}(t) = \max(t, 0)$ is the [ReLU](relu.md) (Remark 5.3 of Telgarsky's deep learning theory lecture notes, Section 5).
