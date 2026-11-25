# For μ > 0, the projection is the minimizer of the energy metric

Let $\mu > 0$ and let $\mathcal K$ be a nonempty convex set of real $3 \times 3$ matrices that is
complete for the Frobenius distance (equivalently, closed). For all real $3 \times 3$ matrices
$s_{\mathrm{trial}}$ and $s$, the
[nearest-point projection](../../../Analysis/hilbert-spaces/hilbert-projection-theorem/convex-projection.md)
of $s_{\mathrm{trial}}$ onto $\mathcal K$ is $s$ if and only if $s \in \mathcal K$ and

$$
\mu\, \|\Delta\varepsilon_p(s_{\mathrm{trial}}, s)\|^2 \le
\mu\, \|\Delta\varepsilon_p(s_{\mathrm{trial}}, \tau)\|^2
\quad \text{for every } \tau \in \mathcal K,
$$

where $\Delta\varepsilon_p(s_{\mathrm{trial}}, \tau) = (s_{\mathrm{trial}} - \tau) / (2\mu)$ is the
[plastic strain increment](plastic-strain-increment.md) and $\|A\|^2 = \sum_{i,j} A_{ij}^2$ the
squared [Frobenius norm](frobenius-inner-eq-sum-mul.md). Each side equals
$\|s_{\mathrm{trial}} - \tau\|^2 / (4\mu)$; for a trace-free $s_{\mathrm{trial}}$ and $\mathcal K$
of trace-free matrices it is the complementary elastic energy of the plastic stress correction, so
the return in this energy metric is the Frobenius projection. The equivalence holds for every matrix
$s_{\mathrm{trial}}$.
