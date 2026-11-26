# Running a concatenated trace

For every initial value $\mathit{init} \in \mathbb{N}$ and traces $xs$, $ys$ of thread-tagged operations,

$$\mathrm{runTrace}(\mathit{init}, xs \mathbin{+\!\!+} ys) = \mathrm{runTrace}(\mathrm{runTrace}(\mathit{init}, xs), ys),$$

so running a concatenation runs $ys$ from the state that $xs$ reaches.
