# Every phase of the repeated session can step

Let $n$ be a natural number, $r$ a polarity and $b$ a name scoped at depth $n$ (a constant, or a
variable with index $< n$) with $b \ne \mathrm{c}_{710}$ and $b \ne \mathrm{c}_{711}$. Then for
every natural number $i$ there is a process $q$ with $\Phi_i(b) \to q$. Here $\Phi_i(b)$ is $P(b)$,
$P_1(b)$ or $P_2(b)$ according as $i \bmod 3$ is $0$, $1$ or $2$. The states are $P(b) = (Q_s(b)
\mid D_s) \mid (Q_r(b) \mid D_r)$, $P_1(b) = (W_s(b) \mid D_s) \mid (Q_r(b) \mid D_r)$ and $P_2(b) =
(W_s(b) \mid D_s) \mid (W_r(b) \mid D_r)$. Here $W_s(b) = \overline{b}\langle
\mathrm{c}_{712}\rangle.\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$ and $W_r(b) =
b(\cdot).\overline{\mathrm{c}_{711}}\langle \uparrow_0 b\rangle.\mathbf{0}$ are the workers, $D_s =
{!\mathrm{c}_{710}(\cdot).W_s(\mathrm{v}_0)}$ and $D_r =
{!\mathrm{c}_{711}(\cdot).W_r(\mathrm{v}_0)}$ the replicated daemons, and $Q_s(b) =
\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$ and $Q_r(b) =
\overline{\mathrm{c}_{711}}\langle b\rangle.\mathbf{0}$ the requests.

The proof goes through the typing $\Gamma_r; I_{b,r} \vdash_n \Phi_i(b)$; the conclusion itself does
not mention $r$ or $n$.
