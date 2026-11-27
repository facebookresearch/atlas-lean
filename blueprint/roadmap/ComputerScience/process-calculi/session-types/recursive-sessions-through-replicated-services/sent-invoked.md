# State after the sender trigger invocation

For a name $b$, the state after the sender invocation is $P_1(b) = (W_s(b) \mid D_s) \mid (Q_r(b)
\mid D_r)$.

Here $W_s(b) = \overline{b}\langle \mathrm{c}_{712}\rangle.\overline{\mathrm{c}_{710}}\langle
b\rangle.\mathbf{0}$ and $W_r(b) = b(\cdot).\overline{\mathrm{c}_{711}}\langle \uparrow_0
b\rangle.\mathbf{0}$ are the workers, $D_s = {!\mathrm{c}_{710}(\cdot).W_s(\mathrm{v}_0)}$ and $D_r
= {!\mathrm{c}_{711}(\cdot).W_r(\mathrm{v}_0)}$ the replicated daemons, and $Q_s(b) =
\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$ and $Q_r(b) =
\overline{\mathrm{c}_{711}}\langle b\rangle.\mathbf{0}$ the requests.
