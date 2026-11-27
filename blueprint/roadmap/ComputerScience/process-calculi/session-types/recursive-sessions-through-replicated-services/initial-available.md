# All declared services are available in the pending state

For every name $b$ and polarity $r$, all services of $\Gamma_r$ are available in $P(b)$: both
declared triggers $\mathrm{c}_{710}$ and $\mathrm{c}_{711}$ are offered by replicated unguarded
inputs.

The states are $P(b) = (Q_s(b) \mid D_s) \mid (Q_r(b) \mid D_r)$, $P_1(b) = (W_s(b) \mid D_s) \mid
(Q_r(b) \mid D_r)$ and $P_2(b) = (W_s(b) \mid D_s) \mid (W_r(b) \mid D_r)$. Here $W_s(b) =
\overline{b}\langle \mathrm{c}_{712}\rangle.\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$
and $W_r(b) = b(\cdot).\overline{\mathrm{c}_{711}}\langle \uparrow_0 b\rangle.\mathbf{0}$ are the
workers, $D_s = {!\mathrm{c}_{710}(\cdot).W_s(\mathrm{v}_0)}$ and $D_r =
{!\mathrm{c}_{711}(\cdot).W_r(\mathrm{v}_0)}$ the replicated daemons, and $Q_s(b) =
\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$ and $Q_r(b) =
\overline{\mathrm{c}_{711}}\langle b\rangle.\mathbf{0}$ the requests. The service environment
$\Gamma_r$ declares $710 \mapsto (0, r, \kappa)$ and $711 \mapsto (0, \bar r, \bar\kappa)$
(priority, polarity of the transferred endpoint, capability), where $\kappa = (7,R)$, $\bar\kappa =
(7,\overline{R})$ and $R$ is the cursor at the single node of the one-node graph whose node sends a
name and loops to itself.
