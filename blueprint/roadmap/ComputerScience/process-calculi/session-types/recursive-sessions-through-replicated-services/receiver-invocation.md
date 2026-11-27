# Sender-invoked state steps by invoking the receiver trigger

For every name $b$, $P_1(b) \to P_2(b)$ in one π-calculus step: the request $Q_r(b)$ is received by
the receiver daemon.

The states are $P(b) = (Q_s(b) \mid D_s) \mid (Q_r(b) \mid D_r)$, $P_1(b) = (W_s(b) \mid D_s) \mid
(Q_r(b) \mid D_r)$ and $P_2(b) = (W_s(b) \mid D_s) \mid (W_r(b) \mid D_r)$. Here $W_s(b) =
\overline{b}\langle \mathrm{c}_{712}\rangle.\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$
and $W_r(b) = b(\cdot).\overline{\mathrm{c}_{711}}\langle \uparrow_0 b\rangle.\mathbf{0}$ are the
workers, $D_s = {!\mathrm{c}_{710}(\cdot).W_s(\mathrm{v}_0)}$ and $D_r =
{!\mathrm{c}_{711}(\cdot).W_r(\mathrm{v}_0)}$ the replicated daemons, and $Q_s(b) =
\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$ and $Q_r(b) =
\overline{\mathrm{c}_{711}}\langle b\rangle.\mathbf{0}$ the requests.
